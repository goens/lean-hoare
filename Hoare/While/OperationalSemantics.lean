import Hoare.While.Syntax
import Hoare.While.Context

namespace While

inductive Expr.Step {Γ : Context} : Expr → Expr → Prop
  | add {n1 n2 : Nat} {e1 e2 : Expr} : Expr.Step e1 (Expr.num n1) → Expr.Step e2 (Expr.num n2) →
      Expr.Step (Expr.add e1 e2) (Expr.num (n1 + n2))
  | sub {n1 n2 : Nat} {e1 e2 : Expr} : Expr.Step e1 (Expr.num n1) → Expr.Step e2 (Expr.num n2) →
      Expr.Step (Expr.sub e1 e2) (Expr.num (n1 - n2))
  | mul {n1 n2 : Nat} {e1 e2 : Expr} : Expr.Step e1 (Expr.num n1) → Expr.Step e2 (Expr.num n2) →
      Expr.Step (Expr.mul e1 e2) (Expr.num (n1 * n2))
  | eq_bool {b1 b2 : Bool} {e1 e2 : Expr} : Expr.Step e1 (Expr.bool b1) → Expr.Step e2 (Expr.bool b2) →
      Expr.Step (Expr.eq e1 e2) (Expr.bool (b1 == b2))
  | eq_num {n1 n2 : Nat} {e1 e2 : Expr} : Expr.Step e1 (Expr.num n1) → Expr.Step e2 (Expr.num n2) →
      Expr.Step (Expr.eq e1 e2) (Expr.bool (n1 == n2))
  | lt {n1 n2 : Nat} {e1 e2 : Expr} : Expr.Step e1 (Expr.num n1) → Expr.Step e2 (Expr.num n2) →
      Expr.Step (Expr.lt e1 e2) (Expr.bool (n1 < n2))
  | gt {n1 n2 : Nat} {e1 e2 : Expr} : Expr.Step e1 (Expr.num n1) → Expr.Step e2 (Expr.num n2) →
      Expr.Step (Expr.gt e1 e2) (Expr.bool (n1 > n2))
  | var {x : String} {v : Val} : Γ.getVal? x = some v → Expr.Step (Expr.var x) v.toExpr

inductive Com.Step : Context × Com → Context × Com → Prop
  | assign {Γ Γ' : Context} {x : String} {e : Expr} {v : Val} :
      @Expr.Step Γ e v.toExpr →
      Com.Step (Γ, Com.assign x e) (Γ.assign x v, Com.skip)
  | seq {Γ₁ Γ₂ Γ₃ : Context} {c₁ c₂ c₃ : Com} :
      Com.Step (Γ₁, c₁) (Γ₂, Com.skip) →
      Com.Step (Γ₂, c₂) (Γ₃, c₃) → Com.Step (Γ₁, Com.seq c₁ c₂) (Γ₃, c₃)
  | cond_true {Γ : Context} {c₁ c₂ : Com} {e : Expr} :
      @Expr.Step Γ e (Expr.bool .true) →
      Com.Step (Γ, Com.cond e c₁ c₂) (Γ, c₁)
  | cond_false {Γ : Context} {c₁ c₂ : Com} {e : Expr} :
      @Expr.Step Γ e (Expr.bool .false) →
      Com.Step (Γ, Com.cond e c₁ c₂) (Γ, c₁)
  | while_true {Γ Γ' : Context} {c : Com} {e : Expr} :
      @Expr.Step Γ e (Expr.bool .true) →
      Com.Step (Γ, Com.while e c) (Γ, Com.seq c (Com.while e c))
  | while_false {Γ : Context} {c : Com} {e : Expr} :
      @Expr.Step Γ e (Expr.bool .false) →
      Com.Step (Γ, Com.while e c) (Γ, Com.skip)

notation G " ⊢ " e " ⟶ " e' => @Expr.Step G e e'
notation G " ⊢ " e " ⟶* " e' =>  Relation.TransGen (@Expr.Step G) e e'

infixl:50 " ⟹ " => Com.Step
infixl:50 " ⟹* " => Relation.TransGen Com.Step

-- `Trans` instances (for `calc`)
instance {Γ : Context} : Trans (@Expr.Step Γ) (Relation.TransGen (@Expr.Step Γ)) (Relation.TransGen (@Expr.Step Γ)) where
  trans h₁ h₂ :=  Relation.TransGen.trans (Relation.TransGen.single h₁) h₂
instance {Γ : Context} : Trans (Relation.TransGen (@Expr.Step Γ)) (@Expr.Step Γ) (Relation.TransGen (@Expr.Step Γ)) where
  trans :=  Relation.TransGen.tail
instance {Γ : Context} : Trans (Relation.TransGen (@Expr.Step Γ)) (Relation.TransGen (@Expr.Step Γ)) (Relation.TransGen (@Expr.Step Γ)) where
  trans :=  Relation.TransGen.trans

end While
