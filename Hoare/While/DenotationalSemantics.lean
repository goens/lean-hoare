import Hoare.While.Syntax
import Hoare.While.Context

namespace While

def Expr.val? (Γ : Context) : Expr → Option Val
  | Expr.num n => Val.num n
  | Expr.bool b => Val.bool b
  | Expr.var x => Γ.getVal? x
  | Expr.add e1 e2 => match e1.val? Γ, e2.val? Γ with
    | some (Val.num n1), some (Val.num n2) => some (Val.num (n1 + n2))
    | _, _ => none
  | Expr.sub e1 e2 => match e1.val? Γ, e2.val? Γ with
    | some (Val.num n1), some (Val.num n2) => some (Val.num (n1 - n2))
    | _, _ => none
  | Expr.mul e1 e2 => match e1.val? Γ, e2.val? Γ with
    | some (Val.num n1), some (Val.num n2) => some (Val.num (n1 * n2))
    | _, _ => none
  | Expr.eq e1 e2 => match e1.val? Γ, e2.val? Γ with
    | some (Val.num n1), some (Val.num n2) => some (Val.bool (n1 == n2))
    | some (Val.bool b1), some (Val.bool b2) => some (Val.bool (b1 == b2))
    | _, _ => none
  | Expr.lt e1 e2 => match e1.val? Γ, e2.val? Γ with
    | some (Val.num n1), some (Val.num n2) => some (Val.bool (n1 < n2))
    | _, _ => none
  | Expr.gt e1 e2 => match e1.val? Γ, e2.val? Γ with
    | some (Val.num n1), some (Val.num n2) => some (Val.bool (n1 > n2))
    | _, _ => none
  | Expr.and e1 e2 => match e1.val? Γ, e2.val? Γ with
    | some (Val.bool b1), some (Val.bool b2) => some (Val.bool (b1 && b2))
    | _, _ => none
  | Expr.or e1 e2 => match e1.val? Γ, e2.val? Γ with
    | some (Val.bool b1), some (Val.bool b2) => some (Val.bool (b1 || b2))
    | _, _ => none


/--
Evaluate the denotation of a command.

Because `while` might not terminate, `Com.eval` is a partial function.
-/
partial def Com.eval (Γ : Context := Context.empty) : Com → Context
  | Com.skip => Γ
  | Com.assign x e => match Expr.val? Γ e with
    | some v => Γ.assign x v
    | none => Γ
  | Com.seq c₁ c₂ => Com.eval (Com.eval Γ c₁) c₂
  | Com.cond e c₁ c₂ => match Expr.val? Γ e with
    | some (Val.bool .true) => Com.eval Γ c₁
    | some (Val.bool .false) => Com.eval Γ c₂
    | _ => Γ
  | Com.while e c => match Expr.val? Γ e with
    | some (Val.bool .true) => Com.eval (Com.eval Γ c) (Com.while e c)
    | some (Val.bool .false) => Γ
    | _ => Γ

syntax ident "⊢" " 〚" expr "〛" : term
syntax "〚" com "〛" : term
macro_rules
| `($Γ:ident ⊢ 〚$e:expr〛) => `(Expr.val? $Γ [expr| $e] )
| `(〚 $c:com 〛) => `(Com.eval Context.empty [com|$c])

-- Not sure why I need to spell this one out to Lean
instance decideVal? {Γ : Context} {e : Expr} : Decidable (e.val? Γ =  some (Val.bool .true)) :=
  match e.val? Γ with
    | some (Val.bool .true) => isTrue rfl
    | some (Val.bool .false) => isFalse (by intro h; cases h)
    | some (Val.num _) => isFalse (by intro h; cases h)
    | none => isFalse (by intro h; cases h)

#eval 〚
  X := 0;
  Y := 0;
  while X < 10 do
    X := X + 1
  od
〛

end While
