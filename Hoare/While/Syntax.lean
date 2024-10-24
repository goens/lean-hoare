-- Based on https://www.cl.cam.ac.uk/archive/mjcg/Teaching/2015/Hoare/Notes/

namespace While

/-- Abstract Syntax of Expressions -/
inductive Expr
| num : Nat → Expr
| bool : Bool → Expr
| var : String → Expr
| add : Expr → Expr → Expr
| sub : Expr → Expr → Expr
| mul : Expr → Expr → Expr
| eq : Expr → Expr → Expr
| lt : Expr → Expr → Expr
| gt : Expr → Expr → Expr
| and : Expr → Expr → Expr
| or : Expr → Expr → Expr
deriving Repr, DecidableEq

inductive Com
| assign : String → Expr → Com
| seq : Com → Com → Com
| cond : Expr → Com → Com → Com
| while : Expr → Com → Com
| skip : Com

-- for : Com → Expr → Com → Com → Com
-- block : Com → Com

-- Concrete syntax
declare_syntax_cat expr
declare_syntax_cat statement
declare_syntax_cat com

syntax num : expr
syntax ident : expr
syntax "true" : expr
syntax "false" : expr
syntax "(" expr ")" : expr
syntax expr " + " expr : expr
syntax expr " - " expr : expr
syntax expr " * " expr : expr
syntax expr " == " expr : expr
syntax expr " < " expr : expr
syntax expr " > " expr : expr
syntax expr " && " expr : expr
syntax expr " || " expr : expr

syntax ident " := " expr : com
syntax com " ; " com : com
syntax "if " expr " then " com " else " com "end" : com
syntax "while " expr " do " com "end" : com

syntax "[expr|" expr "]" : term
syntax "[com|" com "]" : term

macro_rules
| `([expr| $n:num]) => `(Expr.num $n)
| `([expr| $x:ident]) => `(Expr.var $(Lean.quote x.getId.toString))
| `([expr| true]) => `(Expr.bool «true»)
| `([expr| false]) => `(Expr.bool «false»)
| `([expr| $e1 + $e2]) => `(Expr.add [expr| $e1] [expr| $e2])
| `([expr| $e1 - $e2]) => `(Expr.sub [expr| $e1] [expr| $e2])
| `([expr| $e1 * $e2]) => `(Expr.mul [expr| $e1] [expr| $e2])
| `([expr| $e1 == $e2]) => `(Expr.eq [expr| $e1] [expr| $e2])
| `([expr| $e1 < $e2]) => `(Expr.lt [expr| $e1] [expr| $e2])
| `([expr| $e1 > $e2]) => `(Expr.gt [expr| $e1] [expr| $e2])
| `([expr| $e1 && $e2]) => `(Expr.and [expr| $e1] [expr| $e2])
| `([expr| $e1 || $e2]) => `(Expr.or [expr| $e1] [expr| $e2])
| `([com| $x:ident := $e]) => `(Com.assign $(Lean.quote x.getId.toString) [expr| $e])
| `([com| $c1; $c2]) => `(Com.seq [com| $c1] [com| $c2])
| `([com| if $e then $c1 else $c2 end]) => `(Com.cond [expr| $e] [com| $c1] [com| $c2])
| `([com| while $e do $c end]) => `(Com.while [expr| $e] [com| $c])

-- Quasiquotation
syntax "$(" term ")" : expr
syntax "$(" term ")" : com
macro_rules
| `([expr| $($t:term)]) => `($t)
| `([com| $($t:term)]) => `($t)

instance : Coe Nat Expr := ⟨Expr.num⟩
instance : Coe Bool Expr := ⟨Expr.bool⟩

end While
