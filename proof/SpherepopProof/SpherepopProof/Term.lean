/-
Terms of the circle calculus: atoms, constants, scope constructors,
application circles and labelled brackets. This file fixes the concrete
syntax of SPEC.md section 2 as a Lean inductive type. Nothing here knows
about reduction, permissions or hosts.
-/

namespace Spherepop

/-- A label of a bracket or a scope constructor. -/
abbrev Label := String

/-- The six constants of the calculus. `I` and `B` are never gated;
`W`, `K`, `C` and `S` may be gated by the permission structure. -/
inductive Const
  | I | B | C | K | W | S
deriving DecidableEq, Repr

/-- A circle term. `atom` is inert data; `const` is a combinator constant;
`scope l` is the scope constructor `sc_l`; `app f x` is the application
circle `f x`; `bracket l b` is `<b>_l`. -/
inductive Term
  | atom (name : String)
  | const (c : Const)
  | scope (l : Label)
  | app (f x : Term)
  | bracket (l : Label) (body : Term)
deriving DecidableEq, Repr

namespace Term

/-- The number of arguments a contraction headed by `c` consumes. -/
def arity : Const → Nat
  | .I => 1
  | .K => 2
  | .W => 2
  | .B => 3
  | .C => 3
  | .S => 3

/-- `f a1 ... an`, associating to the left. -/
def apply (f : Term) (args : List Term) : Term :=
  args.foldl app f

/-- The head of the application spine of `t` and its arguments, in order.
For a non-application the head is `t` itself and the argument list is
empty. -/
def spine : Term → Term × List Term
  | .app f x =>
      let (h, as) := spine f
      (h, as ++ [x])
  | t => (t, [])

/-- The right-hand side template of each contraction, applied to the
listed arguments. The list must have length `arity c`; other inputs are
mapped to the constant itself and never occur in a redex. -/
def contractTemplate (c : Const) (args : List Term) : Term :=
  match c, args with
  | .I, [a] => a
  | .K, [x, y] => x
  | .W, [f, x] => app (app f x) x
  | .B, [f, g, x] => app f (app g x)
  | .C, [f, x, y] => app (app f y) x
  | .S, [f, g, x] => app (app f x) (app g x)
  | _, _ => const c

end Term

end Spherepop
