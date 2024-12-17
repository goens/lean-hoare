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
| le : Expr → Expr → Expr
| ge : Expr → Expr → Expr
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
syntax expr " <= " expr : expr
syntax expr " > " expr : expr
syntax expr " >= " expr : expr
syntax expr " && " expr : expr
syntax expr " || " expr : expr

syntax ident " := " expr : com
syntax "let " ident " := " expr : com
syntax com "; " com : com
syntax "if " expr " then " com " else " com " fi" : com
syntax "while " expr " do " com " od" : com
syntax "skip " : com

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
| `([expr| $e1 <= $e2]) => `(Expr.le [expr| $e1] [expr| $e2])
| `([expr| $e1 >= $e2]) => `(Expr.ge [expr| $e1] [expr| $e2])
| `([expr| $e1 && $e2]) => `(Expr.and [expr| $e1] [expr| $e2])
| `([expr| $e1 || $e2]) => `(Expr.or [expr| $e1] [expr| $e2])
| `([expr| ($e)]) => `([expr| $e])
| `([com| skip]) => `(Com.skip)
| `([com| let $x:ident := $e]) => `(Com.assign $(Lean.quote x.getId.toString) [expr| $e])
| `([com| $x:ident := $e]) => `(Com.assign $(Lean.quote x.getId.toString) [expr| $e])
| `([com| $c1; $c2]) => `(Com.seq [com| $c1] [com| $c2])
| `([com| if $e then $c1 else $c2 fi]) => `(Com.cond [expr| $e] [com| $c1] [com| $c2])
| `([com| while $e do $c od]) => `(Com.while [expr| $e] [com| $c])

-- Quasiquotation
syntax "$(" term ")" : expr
syntax "$(" term ")" : com
macro_rules
| `([expr| $($t:term)]) => `($t)
| `([com| $($t:term)]) => `($t)

instance : Coe Nat Expr := ⟨Expr.num⟩
instance : Coe Bool Expr := ⟨Expr.bool⟩

instance : Coe Lean.NumLit (Lean.TSyntax `expr) where
  coe s := ⟨s.raw⟩

instance : Coe Lean.Ident (Lean.TSyntax `expr) where
  coe s := ⟨s.raw⟩

-- Unexpanders

@[app_unexpander While.Expr.num]
def unexpandNum : Lean.PrettyPrinter.Unexpander
  | `($_ $x:num) => `([expr| $x])
  | `($_ $x:ident) => `([expr| $($x)])
  | _ => throw ()

@[app_unexpander While.Expr.bool]
def unexpandBool : Lean.PrettyPrinter.Unexpander
  | `($_ Bool.true) => `([expr| true])
  | `($_ Bool.false) => `([expr| false])
  | `($_ «true») => `([expr| true])
  | `($_ «false») => `([expr| false])
  | `($_ $x:ident) => `([expr| $(x)])
  | _ => throw ()

@[app_unexpander While.Expr.var]
def unexpandIdent : Lean.PrettyPrinter.Unexpander
  | `($_ $x:str) =>
    let identLit := Lean.mkIdent $ Lean.Name.mkSimple x.getString
    `([expr| $identLit])
  | `($_ $x:ident) => `([expr| $($x)])
  | _ => throw ()

@[app_unexpander While.Expr.add]
def unexpandAdd : Lean.PrettyPrinter.Unexpander
  | `($_ [expr| $x] [expr| $y]) => `([expr| $x + $y])
  | _ => throw ()

@[app_unexpander While.Expr.sub]
def unexpandSub : Lean.PrettyPrinter.Unexpander
  | `($_ [expr| $x] [expr| $y]) => `([expr| $x - $y])
  | _ => throw ()

@[app_unexpander While.Expr.mul]
def unexpandMul : Lean.PrettyPrinter.Unexpander
  | `($_ [expr| $x] [expr| $y]) => `([expr| $x * $y])
  | _ => throw ()

@[app_unexpander While.Expr.eq]
def unexpandEq : Lean.PrettyPrinter.Unexpander
  | `($_ [expr| $x] [expr| $y]) => `([expr| $x == $y])
  | _ => throw ()

@[app_unexpander While.Expr.lt]
def unexpandLt : Lean.PrettyPrinter.Unexpander
  | `($_ [expr| $x] [expr| $y]) => `([expr| $x < $y])
  | _ => throw ()

@[app_unexpander While.Expr.gt]
def unexpandGt : Lean.PrettyPrinter.Unexpander
  | `($_ [expr| $x] [expr| $y]) => `([expr| $x > $y])
  | _ => throw ()

@[app_unexpander While.Expr.le]
def unexpandLe : Lean.PrettyPrinter.Unexpander
  | `($_ [expr| $x] [expr| $y]) => `([expr| $x <= $y])
  | _ => throw ()

@[app_unexpander While.Expr.ge]
def unexpandGe : Lean.PrettyPrinter.Unexpander
  | `($_ [expr| $x] [expr| $y]) => `([expr| $x >= $y])
  | _ => throw ()

@[app_unexpander While.Expr.and]
def unexpandAnd : Lean.PrettyPrinter.Unexpander
  | `($_ [expr| $x] [expr| $y]) => `([expr| $x && $y])
  | _ => throw ()

@[app_unexpander While.Expr.or]
def unexpandOr : Lean.PrettyPrinter.Unexpander
  | `($_ [expr| $x] [expr| $y]) => `([expr| $x || $y])
  | _ => throw ()

@[app_unexpander While.Com.skip]
def unexpandSkip : Lean.PrettyPrinter.Unexpander
  | `($_) => `([com| skip])

@[app_unexpander While.Com.seq]
def unexpandSeq : Lean.PrettyPrinter.Unexpander
  | `($_ [com| $c1] [com| $c2]) => `([com| $c1; $c2])
  | _ => throw ()

@[app_unexpander While.Com.cond]
def unexpandCond : Lean.PrettyPrinter.Unexpander
  | `($_ [expr| $e] [com| $c1] [com| $c2]) => `([com| if $e then $c1 else $c2 fi])
  | _ => throw ()

@[app_unexpander While.Com.while]
def unexpandWhile : Lean.PrettyPrinter.Unexpander
  | `($_ [expr| $e] [com| $c]) => `([com| while $e do $c od])
  | _ => throw ()

@[app_unexpander While.Com.assign]
def unexpandAssign : Lean.PrettyPrinter.Unexpander
  | `($_ $x:str  [expr| $e:expr]) =>
    let xl := Lean.mkIdent $ Lean.Name.mkSimple x.getString
    `([com| let $xl := $e])
  | _ => throw ()


def addBinOp (opString : String) (e₁ e₂ : Std.Format) : Std.Format :=
 e₁ ++ opString ++ e₂

open Std

def Expr.reprPrec (e : Expr) (prec : Nat) : Format := match e with
    | .num n => Repr.reprPrec n prec
    | .bool b => Repr.reprPrec b prec
    | .var v => v
    | .add e₁ e₂ => addBinOp " + " (Expr.reprPrec e₁ prec) (Expr.reprPrec e₂ prec)
    | .sub e₁ e₂ => addBinOp " - " (Expr.reprPrec e₁ prec) (Expr.reprPrec e₂ prec)
    | .mul e₁ e₂ => addBinOp " * " (Expr.reprPrec e₁ prec) (Expr.reprPrec e₂ prec)
    | .or e₁ e₂ => addBinOp " || " (Expr.reprPrec e₁ prec) (Expr.reprPrec e₂ prec)
    | .and e₁ e₂ => addBinOp " && " (Expr.reprPrec e₁ prec) (Expr.reprPrec e₂ prec)
    | .ge e₁ e₂ => addBinOp " >= " (Expr.reprPrec e₁ prec) (Expr.reprPrec e₂ prec)
    | .le e₁ e₂ => addBinOp " <= " (Expr.reprPrec e₁ prec) (Expr.reprPrec e₂ prec)
    | .lt e₁ e₂ => addBinOp " < " (Expr.reprPrec e₁ prec) (Expr.reprPrec e₂ prec)
    | .gt e₁ e₂ => addBinOp " > " (Expr.reprPrec e₁ prec) (Expr.reprPrec e₂ prec)
    | .eq e₁ e₂ => addBinOp " == " (Expr.reprPrec e₁ prec) (Expr.reprPrec e₂ prec)

instance : Repr Expr := ⟨Expr.reprPrec⟩

  def Com.reprPrec (c : Com) (prec : Nat) : Format := match c with
    | .skip => "skip"
    | .assign v e => v ++ " := " ++ Repr.reprPrec e prec
    | .seq c₁ c₂ => reprPrec c₁ prec ++ ";" ++ Format.line ++ reprPrec c₂ prec
    | .cond b c₁ c₂ => "if" ++ Format.line ++ (Repr.reprPrec b prec) ++ reprPrec c₁ prec ++ ";" ++ Format.line ++ reprPrec c₂ prec ++ Format.line ++ "fi"
    | .while b c => "while" ++ Format.line ++ (Repr.reprPrec b prec) ++ " do " ++ Format.line ++ reprPrec c prec ++ Format.line ++ "od"

instance : Repr Com := ⟨Com.reprPrec⟩

end While
