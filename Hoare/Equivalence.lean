import Hoare.Statements
import Hoare.While.Types

namespace While

namespace Expr

def equiv (P Q : Expr) : Prop := ∀ (Γ : Context),
  P.val? Γ = Q.val? Γ

theorem equiv_symm {P Q : Expr} : equiv P Q → equiv Q P :=
  fun h Γ => Eq.symm (h Γ)

theorem equiv_trans {P Q R : Expr} : equiv P Q → equiv Q R → equiv P R := by
  intro h1 h2 Γ
  rw [h1,h2]

theorem equiv_refl (P : Expr) : equiv P P := fun Γ => Eq.refl (val? Γ P)

instance : Equivalence equiv where
  refl := equiv_refl
  symm := equiv_symm
  trans := equiv_trans

end Expr

namespace Statement

def equiv' (S T : Statement) : Prop := ∀ (Γ : Context), S.eval Γ ↔ T.eval Γ

theorem equiv'_equiv_eval (S T : Statement) : equiv' S T ↔ ∀ Γ,(Statement.equiv S T).eval Γ := by
  simp [equiv', eval]

theorem equiv_symm {P Q : Statement} : equiv' P Q → equiv' Q P := by
  intro h Γ
  rw [h]

theorem equiv_trans {P Q R : Statement} : equiv' P Q → equiv' Q R → equiv' P R := by
  intro h1 h2 Γ
  rw [h1,h2]

theorem equiv_refl (P : Statement) : equiv' P P := by
  intro Γ
  rfl

instance : Equivalence equiv' where
  refl := equiv_refl
  symm := equiv_symm
  trans := equiv_trans

theorem equiv_expr_equiv_atoms {e₁ e₂ : Expr} :
   e₁.equiv e₂ → (Statement.atom e₁).equiv' (Statement.atom e₂) := by
  simp [Expr.equiv]
  intro h Γ
  specialize h Γ
  simp [eval]
  rw [h]

/-
theorem equiv_well_typed (e₁ e₂ : Expr) :
  e₁.equiv e₂ → ∀ ty, WellTyped e₁ ty ↔ WellTyped e₂ ty := by
  intro h ty
  ... probably needs type signatures etc
-/

theorem bool_atoms_bool_expr_equiv {e₁ e₂ : Expr} :
  (Statement.atom e₁).equiv' (Statement.atom e₂) → e₁.isBool → e₁.equiv e₂ := by
  intro hequiv hbool
  simp [equiv', Statement.eval] at hequiv





end Statement

end While
