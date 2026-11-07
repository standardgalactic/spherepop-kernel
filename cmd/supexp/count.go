package main

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"sort"
	"strings"
)

const modulePath = "github.com/standardgalactic/spherepop-kernel/"

var modulePkgs = []string{"term", "reduce", "trace", "supervised"}

type fileInfo struct {
	imports map[string]string // local name -> module package name
	lines   []string
}

type decl struct {
	pkg   string
	name  string
	recv  string
	node  ast.Node
	file  *fileInfo
	lines int
}

type pkgInfo struct {
	decls   []*decl
	byName  map[string][]*decl // functions
	methods map[string][]*decl
	imports map[string]bool // module packages imported by non-test files
}

type module map[string]*pkgInfo

func loadModule(root string) (module, error) {
	mod := module{}
	for _, name := range modulePkgs {
		pi := &pkgInfo{byName: map[string][]*decl{}, methods: map[string][]*decl{}, imports: map[string]bool{}}
		mod[name] = pi
		dir := filepath.Join(root, name)
		ents, err := os.ReadDir(dir)
		if err != nil {
			return nil, err
		}
		for _, e := range ents {
			fn := e.Name()
			if e.IsDir() || !strings.HasSuffix(fn, ".go") || strings.HasSuffix(fn, "_test.go") {
				continue
			}
			src, err := os.ReadFile(filepath.Join(dir, fn))
			if err != nil {
				return nil, err
			}
			fset := token.NewFileSet()
			f, err := parser.ParseFile(fset, fn, src, parser.ParseComments)
			if err != nil {
				return nil, err
			}
			fi := &fileInfo{imports: map[string]string{}, lines: strings.Split(string(src), "\n")}
			for _, im := range f.Imports {
				p := strings.Trim(im.Path.Value, `"`)
				if !strings.HasPrefix(p, modulePath) {
					continue
				}
				short := strings.TrimPrefix(p, modulePath)
				local := short[strings.LastIndex(short, "/")+1:]
				if im.Name != nil {
					local = im.Name.Name
				}
				fi.imports[local] = short
				pi.imports[short] = true
			}
			add := func(n ast.Node, names []string, recv string) {
				d := &decl{pkg: name, node: n, file: fi, recv: recv}
				d.lines = countLines(fi.lines, fset.Position(n.Pos()).Line, fset.Position(n.End()).Line)
				pi.decls = append(pi.decls, d)
				for _, nm := range names {
					if nm == "_" {
						continue
					}
					if recv != "" {
						pi.methods[nm] = append(pi.methods[nm], d)
					} else {
						pi.byName[nm] = append(pi.byName[nm], d)
					}
				}
			}
			for _, d := range f.Decls {
				switch x := d.(type) {
				case *ast.FuncDecl:
					recv := ""
					if x.Recv != nil && len(x.Recv.List) == 1 {
						recv = strings.TrimPrefix(types(x.Recv.List[0].Type), "*")
					}
					add(x, []string{x.Name.Name}, recv)
				}
			}
		}
	}
	return mod, nil
}

func types(e ast.Expr) string {
	switch x := e.(type) {
	case *ast.Ident:
		return x.Name
	case *ast.StarExpr:
		return "*" + types(x.X)
	case *ast.IndexExpr:
		return types(x.X)
	}
	return ""
}

// countLines counts the non-blank, non-comment lines in lines[from-1:to].
func countLines(lines []string, from, to int) int {
	n, inBlock := 0, false
	for i := from - 1; i < to && i < len(lines); i++ {
		s := strings.TrimSpace(lines[i])
		if inBlock {
			if j := strings.Index(s, "*/"); j >= 0 {
				inBlock = false
				s = strings.TrimSpace(s[j+2:])
			} else {
				continue
			}
		}
		if strings.HasPrefix(s, "/*") {
			if !strings.Contains(s, "*/") {
				inBlock = true
			}
			continue
		}
		if s == "" || strings.HasPrefix(s, "//") {
			continue
		}
		n++
	}
	return n
}

type root struct{ pkg, name, recv string }

// find returns the declaration named name (a method of recv if recv is set).
func (m module) find(r root) []*decl {
	var out []*decl
	pi := m[r.pkg]
	if r.recv != "" {
		for _, d := range pi.methods[r.name] {
			if d.recv == r.recv {
				out = append(out, d)
			}
		}
		return out
	}
	return pi.byName[r.name]
}

// reachable returns the functions and methods reachable by name from the roots,
// looking only in the allowed packages. A bare identifier resolves within
// the declaration's own package, pkg.Name resolves in the imported module
// package, and x.Name, which cannot be resolved without types, resolves to
// every method called Name in the allowed packages.
func (m module) reachable(allowed map[string]bool, roots []root) map[*decl]bool {
	seen := map[*decl]bool{}
	var queue []*decl
	push := func(ds []*decl) {
		for _, d := range ds {
			if allowed[d.pkg] && !seen[d] {
				seen[d] = true
				queue = append(queue, d)
			}
		}
	}
	for _, r := range roots {
		push(m.find(r))
	}
	for len(queue) > 0 {
		d := queue[0]
		queue = queue[1:]
		var visit func(n ast.Node) bool
		visit = func(n ast.Node) bool {
			switch x := n.(type) {
			case *ast.SelectorExpr:
				if id, ok := x.X.(*ast.Ident); ok {
					if p, ok := d.file.imports[id.Name]; ok {
						if allowed[p] {
							push(m[p].byName[x.Sel.Name])
						}
						return false
					}
				}
				for p := range allowed {
					push(m[p].methods[x.Sel.Name])
				}
				ast.Inspect(x.X, visit)
				return false
			case *ast.Ident:
				push(m[d.pkg].byName[x.Name])
			}
			return true
		}
		ast.Inspect(d.node, visit)
	}
	return seen
}

type tally struct {
	lines, decls int
	byPkg        map[string]int
}

func summarise(set map[*decl]bool) tally {
	t := tally{byPkg: map[string]int{}}
	for d := range set {
		t.lines += d.lines
		t.decls++
		t.byPkg[d.pkg] += d.lines
	}
	return t
}

func (t tally) String() string {
	var ps []string
	for p := range t.byPkg {
		ps = append(ps, p)
	}
	sort.Strings(ps)
	var parts []string
	for _, p := range ps {
		parts = append(parts, fmt.Sprintf("%s %d", p, t.byPkg[p]))
	}
	return fmt.Sprintf("%4d lines in %3d declarations (%s)", t.lines, t.decls, strings.Join(parts, ", "))
}

func minus(a, b map[*decl]bool) map[*decl]bool {
	out := map[*decl]bool{}
	for d := range a {
		if !b[d] {
			out[d] = true
		}
	}
	return out
}

func (m module) allowedFor(pkg string) map[string]bool {
	a := map[string]bool{pkg: true}
	for p := range m[pkg].imports {
		if _, ok := m[p]; ok {
			a[p] = true
		}
	}
	return a
}

func runCount() error {
	mod, err := loadModule(".")
	if err != nil {
		return fmt.Errorf("run from the module root: %w", err)
	}
	scoped := mod.reachable(mod.allowedFor("trace"), []root{{"trace", "Check", ""}})
	replay := mod.reachable(mod.allowedFor("supervised"), []root{{"supervised", "CheckReplay", ""}})
	logOnly := mod.reachable(mod.allowedFor("supervised"), []root{{"supervised", "CheckLog", ""}})
	apply := mod.reachable(map[string]bool{"reduce": true, "term": true}, []root{{"reduce", "Apply", "Config"}})

	fmt.Println("trusted code reachable from the function that accepts an outcome")
	fmt.Println("  counting rule: function and method declarations reachable by name from the root within the root's own package and the module packages it imports, non-blank non-comment lines, test files excluded")
	fmt.Printf("  scoped design, root trace.Check:                %s\n", summarise(scoped))
	fmt.Printf("  supervised design, root CheckReplay:            %s\n", summarise(replay))
	fmt.Printf("  supervised design, root CheckLog (no replay):   %s\n", summarise(logOnly))
	fmt.Printf("  shared closure of reduce.Apply:                 %s\n", summarise(apply))
	fmt.Printf("  trace.Check beyond the Apply closure:           %s\n", summarise(minus(scoped, apply)))
	fmt.Printf("  CheckReplay beyond the Apply closure:           %s\n", summarise(minus(replay, apply)))
	fmt.Printf("  CheckLog beyond the Apply closure:              %s\n", summarise(minus(logOnly, apply)))
	total := 0
	for _, p := range []string{"term", "reduce", "trace", "supervised"} {
		n := 0
		for _, d := range mod[p].decls {
			n += d.lines
		}
		total += n
		fmt.Printf("  all non-test functions and methods in %-11s %d lines\n", p+":", n)
	}
	fmt.Printf("  all four packages: %d lines\n", total)
	return nil
}
