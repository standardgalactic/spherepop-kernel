"""Cut listings for the book directly from the tested source files."""
import ast, os, textwrap
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
OUT = os.path.join(ROOT, "out")


def src(p):
    with open(os.path.join(ROOT, p)) as f:
        return f.read()


def fn(path, qual):
    text = src(path); lines = text.split("\n"); tree = ast.parse(text)
    parts = qual.split(".")
    nodes = tree.body
    for i, p in enumerate(parts):
        node = next(n for n in nodes if getattr(n, "name", None) == p)
        nodes = getattr(node, "body", [])
    start = min([node.lineno] + [d.lineno for d in node.decorator_list]) - 1
    return textwrap.dedent("\n".join(lines[start:node.end_lineno]))


def between(path, a, b):
    text = src(path).split("\n")
    i = next(k for k, l in enumerate(text) if a in l)
    j = next(k for k, l in enumerate(text) if k > i and b in l)
    return textwrap.dedent("\n".join(text[i:j])).rstrip()


E = {
    "ex_kernel_prims": between("spop/kernel.py", "# the four primitives", "# admissibility and application"),
    "ex_kernel_commit": between("spop/kernel.py", "def _commit", "# evidence and acceptance"),
    "ex_kernel_replay": between("spop/kernel.py", "@classmethod", "# derived forms"),
    "ex_kernel_derived": between("spop/kernel.py", "# derived forms", "def apply_via"),
    "ex_regs_edge": fn("spop/regs.py", "ShiftRegister.edge"),
    "ex_regs_ripple": fn("spop/regs.py", "RippleRegister.edge"),
    "ex_regs_transfer": fn("spop/regs.py", "TransferRegister.clock"),
    "ex_forth_stack": between("spop/forth.py", 'elif name == "dup":', 'elif name == "2dup":'),
    "ex_forth_if": between("spop/forth.py", 'elif k == "if":', 'elif k == "until":'),
    "ex_forth_call": fn("spop/forth.py", "Forth.call"),
    "ex_forth_explain": fn("spop/forth.py", "Forth.explain"),
    "ex_lisp_env": "\n\n".join(fn("spop/lisp.py", "Lisp." + n) for n in ("define", "set_bang", "lineage", "make_closure")),
    "ex_lisp_eval": fn("spop/lisp.py", "Lisp.eval"),
    "ex_lisp_call": between("spop/lisp.py", "            args = [self.eval(a, env) for a in x[1:]]", "            if isinstance(f, Builtin):"),
    "ex_lisp_macro": fn("spop/lisp.py", "match") + "\n\n" + fn("spop/lisp.py", "expand"),
    "ex_racket_module": "\n\n".join(fn("spop/racket.py", "Racket." + n) for n in ("_module", "_require")),
    "ex_racket_find": fn("spop/racket.py", "Racket._find") + "\n\n" + fn("spop/racket.py", "Racket.where"),
    "ex_basic_enter": fn("spop/basic.py", "Basic.enter") + "\n\n" + fn("spop/basic.py", "Basic.put"),
    "ex_basic_load": fn("spop/basic.py", "Basic.load"),
    "ex_basic_gosub": between("spop/basic.py", 'elif sig[0] == "gosub":', 'elif sig[0] == "goback":'),
    "ex_shell_resolve": fn("spop/shell.py", "Shell.resolve"),
    "ex_index_flat": fn("spop/index.py", "Index.solve_flat"),
    "ex_index_nested": fn("spop/index.py", "Index.solve_nested") + "\n\n" + fn("spop/index.py", "Index.node_lookup"),
    "ex_index_sync": fn("spop/index.py", "Index.sync_racket"),
}
for k, v in E.items():
    with open(os.path.join(OUT, k + ".txt"), "w") as f:
        f.write(v.rstrip() + "\n")
print("excerpts:", len(E))
