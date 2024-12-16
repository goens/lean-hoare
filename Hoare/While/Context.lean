import Hoare.While.Syntax

namespace While

inductive Val
  | num : Nat → Val
  | bool : Bool → Val

-- Some Coercions
instance : Coe Nat Val := ⟨Val.num⟩
instance : Coe Bool Val := ⟨Val.bool⟩
instance {n : Nat} : CoeDep Val (Val.num n) Nat := ⟨n⟩
instance {b : Bool} : CoeDep Val (Val.bool b) Bool := ⟨b⟩
instance : OfNat Val n := ⟨Val.num n⟩

def Val.toExpr : Val → Expr
  | Val.num n => Expr.num n
  | Val.bool b => Expr.bool b

instance : Repr Val where
  reprPrec
    | Val.num n => reprPrec n
    | Val.bool b => reprPrec b

instance : Coe Val Expr := ⟨Val.toExpr⟩

abbrev Context := List (String × Val)
def Context.getVal? (ctx : Context) (x : String) : Option Val := ctx.lookup x
def Context.assign (ctx : Context) (x : String) (v : Val) : Context :=
  match ctx.lookup x with
    | none  => (x, v) :: ctx
    | some _ =>  ctx.map (fun (x', v') => if x' == x then (x, v) else (x', v'))
def Context.empty : Context := []

instance : EmptyCollection Context := ⟨Context.empty⟩

def Context.reprPrec : Context → Nat → Std.Format
  | [], _ => Std.Format.nil
  | (x, v) :: ctx, n => x ++ " ↦ " ++ repr v ++ "; " ++ reprPrec ctx n

-- Syntactic sugar
declare_syntax_cat ctx

syntax  ident " ↦ " term " ;" ctx : ctx
syntax  ident " ↦ " term : ctx
syntax "[" ctx "]c" : term
macro_rules
  | `([ $x:ident ↦ $v:term ; $c:ctx ]c) =>
    let xs := Lean.quote x.getId.toString
    `(List.cons (Prod.mk $xs $v) [$c]c)
  | `([ $x:ident ↦ $v:term]c) =>
    let xs := Lean.quote x.getId.toString
    `(List.cons (Prod.mk $xs $v) List.nil)


-- Probably not doing the prec thing right
instance : Repr Context := ⟨Context.reprPrec⟩

private def testCtxt : Context := [ x ↦ 1]c
#print testCtxt

end While
