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

-- Probably not doing the prec thing right
instance : Repr Context := ⟨Context.reprPrec⟩

end While
