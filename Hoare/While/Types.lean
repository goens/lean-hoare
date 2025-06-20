import Hoare.While.Syntax
namespace While

inductive Ty
| num : Ty
| bool : Ty
deriving Repr, DecidableEq

inductive WellTyped : Expr → Ty → Prop
| num : WellTyped (Expr.num _) Ty.num
| bool : WellTyped (Expr.bool _) Ty.bool
| add : ∀ e1 e2, WellTyped e1 Ty.num → WellTyped e2 Ty.num →
    WellTyped (Expr.add e1 e2) Ty.num
| sub : ∀ e1 e2, WellTyped e1 Ty.num → WellTyped e2 Ty.num →
    WellTyped (Expr.sub e1 e2) Ty.num
| mul : ∀ e1 e2, WellTyped e1 Ty.num → WellTyped e2 Ty.num →
    WellTyped (Expr.mul e1 e2) Ty.num
| eq : ∀ e1 e2 t, WellTyped e1 t → WellTyped e2 t →
    WellTyped (Expr.eq e1 e2) Ty.bool
| lt : ∀ e1 e2, WellTyped e1 Ty.num → WellTyped e2 Ty.num →
    WellTyped (Expr.lt e1 e2) Ty.bool
| gt : ∀ e1 e2, WellTyped e1 Ty.num → WellTyped e2 Ty.num →
    WellTyped (Expr.gt e1 e2) Ty.bool
| le : ∀ e1 e2, WellTyped e1 Ty.num → WellTyped e2 Ty.num →
    WellTyped (Expr.le e1 e2) Ty.bool
| ge : ∀ e1 e2, WellTyped e1 Ty.num → WellTyped e2 Ty.num →
    WellTyped (Expr.ge e1 e2) Ty.bool
| and : ∀ e1 e2, WellTyped e1 Ty.bool → WellTyped e2 Ty.bool →
    WellTyped (Expr.and e1 e2) Ty.bool
| or : ∀ e1 e2, WellTyped e1 Ty.bool → WellTyped e2 Ty.bool →
    WellTyped (Expr.or e1 e2) Ty.bool

theorem WellTyped.unique : ∀ {e t1 t2}, WellTyped e t1 → WellTyped e t2 → t1 = t2 := by
  intro e t1 t2 h1 h2
  cases h1 <;> cases h2 <;> rfl

def Expr.ty : Expr → Option Ty
  | Expr.num _ => Ty.num
  | Expr.bool _ => Ty.bool
  | Expr.add e1 e2 => if e1.ty = some .num ∧ e2.ty = some .num then some .num else none
  | Expr.sub e1 e2 => if e1.ty = some .num ∧ e2.ty = some .num then some .num else none
  | Expr.mul e1 e2 => if e1.ty = some .num ∧ e2.ty = some .num then some .num else none
  | Expr.eq e1 e2 => if e1.ty = e2.ty ∧ e1.ty.isSome then some .bool else none
  | Expr.lt e1 e2 => if e1.ty = some .num ∧ e2.ty = some .num then some .bool else none
  | Expr.gt e1 e2 => if e1.ty = some .num ∧ e2.ty = some .num then some .bool else none
  | Expr.le e1 e2 => if e1.ty = some .num ∧ e2.ty = some .num then some .bool else none
  | Expr.ge e1 e2 => if e1.ty = some .num ∧ e2.ty = some .num then some .bool else none
  | Expr.and e1 e2 => if e1.ty = some .bool ∧ e2.ty = some .bool then some .bool else none
  | Expr.or e1 e2 => if e1.ty = some .bool ∧ e2.ty = some .bool then some .bool else none
  | Expr.var _ => none -- typing not supported for variables yet...

theorem WellTyped.not_eq_not_eq_ty {e1 e2 : Expr} {t1 t2 : Ty} :
  WellTyped e1 t1 → WellTyped e2 t2 → t1 ≠ t2 → ∀ t, ¬ (WellTyped (Expr.eq e1 e2) t) := by
  intro h1 h2 h3 t h4
  cases h4
  · case eq t h1' h2' =>
      have ht1 : t1 = t := WellTyped.unique h1 h1'
      have ht2 : t2 = t := WellTyped.unique h2 h2'
      rw [ht1, ht2] at h3
      contradiction

theorem WellTyped.not_welltyped_not_eq_ty {e1 e2 : Expr} {t : Ty} :
  WellTyped e1 t → ¬ WellTyped e2 t → ∀ t', ¬ (WellTyped (Expr.eq e1 e2) t') := by
  intro h1 h2 t' h3
  cases h3
  · case eq t' h1' h2' =>
      have ht : t = t' := WellTyped.unique h1 h1'
      apply h2
      rw [ht]
      exact h2'

def WellTyped.decide (e : Expr) (ty : Ty) : Decidable (WellTyped e ty) :=
  match e with
    | Expr.num _ => match ty with
      | .num => isTrue WellTyped.num
      | .bool => isFalse (by intro h; cases h)
    | Expr.bool _ => match ty with
      | .num => isFalse (by intro h; cases h)
      | .bool => isTrue WellTyped.bool
    | Expr.add e1 e2 => match ty with
      | .num => match WellTyped.decide e1 Ty.num with
        | isTrue h1 => match WellTyped.decide e2 Ty.num with
           | isTrue h2 => isTrue (WellTyped.add e1 e2 h1 h2)
           | isFalse h2 => isFalse (by intro h; cases h; simp_all)
        | isFalse h1  => isFalse (by intro h; cases h; simp_all)
      | .bool => isFalse (by intro h; cases h)
    | Expr.sub e1 e2 => match ty with
      | .num => match WellTyped.decide e1 Ty.num with
        | isTrue h1 => match WellTyped.decide e2 Ty.num with
           | isTrue h2 => isTrue (WellTyped.sub e1 e2 h1 h2)
           | isFalse h2 => isFalse (by intro h; cases h; simp_all)
        | isFalse h1  => isFalse (by intro h; cases h; simp_all)
      | .bool => isFalse (by intro h; cases h)
    | Expr.mul e1 e2 => match ty with
      | .num => match WellTyped.decide e1 Ty.num with
        | isTrue h1 => match WellTyped.decide e2 Ty.num with
           | isTrue h2 => isTrue (WellTyped.mul e1 e2 h1 h2)
           | isFalse h2 => isFalse (by intro h; cases h; simp_all)
        | isFalse h1  => isFalse (by intro h; cases h; simp_all)
      | .bool => isFalse (by intro h; cases h)
    | Expr.eq e1 e2 => match ty with
      | .num => isFalse (by intro h; cases h)
      | .bool => match WellTyped.decide e1 Ty.num with
        | isTrue h1 => match WellTyped.decide e2 Ty.num with
           | isTrue h2 => isTrue (WellTyped.eq e1 e2 .num h1 h2)
           | isFalse h2 => isFalse (by intro h; cases h; case eq t' h1' h2' => apply WellTyped.not_welltyped_not_eq_ty h1 h2 .bool (WellTyped.eq e1 e2 t' h1' h2'))
        | isFalse _ =>  match WellTyped.decide e1 Ty.bool with
          | isTrue h1 => match WellTyped.decide e2 Ty.bool with
             | isTrue h2 => isTrue (WellTyped.eq e1 e2 .bool h1 h2)
             | isFalse h2 => isFalse (by intro h; cases h; case eq t' h1' h2' => apply WellTyped.not_welltyped_not_eq_ty h1 h2 .bool (WellTyped.eq e1 e2 t' h1' h2'))
          | isFalse h1 => isFalse (by intro h; cases h; case eq t' h1' h2' => cases t' <;> simp_all)
    | Expr.lt e1 e2 => match ty with
      | .num => isFalse (by intro h; cases h)
      | .bool => match WellTyped.decide e1 Ty.num with
        | isTrue h1 => match WellTyped.decide e2 Ty.num with
           | isTrue h2 => isTrue (WellTyped.lt e1 e2 h1 h2)
           | isFalse h2 => isFalse (by intro h; cases h; simp_all)
        | isFalse h1  => isFalse (by intro h; cases h; simp_all)
    | Expr.gt e1 e2 => match ty with
      | .num => isFalse (by intro h; cases h)
      | .bool => match WellTyped.decide e1 Ty.num with
        | isTrue h1 => match WellTyped.decide e2 Ty.num with
           | isTrue h2 => isTrue (WellTyped.gt e1 e2 h1 h2)
           | isFalse h2 => isFalse (by intro h; cases h; simp_all)
        | isFalse h1  => isFalse (by intro h; cases h; simp_all)
    | Expr.le e1 e2 => match ty with
      | .num => isFalse (by intro h; cases h)
      | .bool => match WellTyped.decide e1 Ty.num with
        | isTrue h1 => match WellTyped.decide e2 Ty.num with
           | isTrue h2 => isTrue (WellTyped.le e1 e2 h1 h2)
           | isFalse h2 => isFalse (by intro h; cases h; simp_all)
        | isFalse h1  => isFalse (by intro h; cases h; simp_all)
    | Expr.ge e1 e2 => match ty with
      | .num => isFalse (by intro h; cases h)
      | .bool => match WellTyped.decide e1 Ty.num with
        | isTrue h1 => match WellTyped.decide e2 Ty.num with
           | isTrue h2 => isTrue (WellTyped.ge e1 e2 h1 h2)
           | isFalse h2 => isFalse (by intro h; cases h; simp_all)
        | isFalse h1  => isFalse (by intro h; cases h; simp_all)
    | Expr.and e1 e2 => match ty with
      | .num => isFalse (by intro h; cases h)
      | .bool => match WellTyped.decide e1 Ty.bool with
        | isTrue h1 => match WellTyped.decide e2 Ty.bool with
           | isTrue h2 => isTrue (WellTyped.and e1 e2 h1 h2)
           | isFalse h2 => isFalse (by intro h; cases h; simp_all)
        | isFalse h1  => isFalse (by intro h; cases h; simp_all)
    | Expr.or e1 e2 => match ty with
      | .num => isFalse (by intro h; cases h)
      | .bool => match WellTyped.decide e1 Ty.bool with
        | isTrue h1 => match WellTyped.decide e2 Ty.bool with
           | isTrue h2 => isTrue (WellTyped.or e1 e2 h1 h2)
           | isFalse h2 => isFalse (by intro h; cases h; simp_all)
        | isFalse h1  => isFalse (by intro h; cases h; simp_all)
    | Expr.var _ => isFalse (by intro h; cases h) -- typing not supported for variables yet...

instance {e : Expr} {ty : Ty} : Decidable (WellTyped e ty) := WellTyped.decide e ty

theorem WellTyped.ty_some {e ty} : WellTyped e ty → e.ty = some ty :=
  by
    intro h
    induction h
    case num => rfl
    case bool => rfl
    case add _ _ h1 h2 => simp [Expr.ty, h1, h2]
    case sub _ _ h1 h2 => simp [Expr.ty, h1, h2]
    case mul _ _ h1 h2 => simp [Expr.ty, h1, h2]
    case eq e1 _ _ h1 h2 => simp [Expr.ty, h1, h2]
    case lt _ _ h1 h2 => simp [Expr.ty, h1, h2]
    case gt _ _ h1 h2 => simp [Expr.ty, h1, h2]
    case le _ _ h1 h2 => simp [Expr.ty, h1, h2]
    case ge _ _ h1 h2 => simp [Expr.ty, h1, h2]
    case and _ _ h1 h2 => simp [Expr.ty, h1, h2]
    case or _ _ h1 h2 => simp [Expr.ty, h1, h2]

theorem WellTyped.some_ty {e ty} : e.ty = some ty → WellTyped e ty := by
  intro h
  induction e generalizing ty <;> simp_all [Expr.ty]
  case num _ => rw [← h]; exact WellTyped.num
  case bool _ => rw [← h]; exact WellTyped.bool
  case add e1 e2 ih_e1 ih_e2 =>
    have h' := h.2.symm; subst h'; exact WellTyped.add e1 e2 ih_e1 ih_e2
  case sub e1 e2 ih_e1 ih_e2 =>
    have h' := h.2.symm; subst h'; exact WellTyped.sub e1 e2 ih_e1 ih_e2
  case mul e1 e2 ih_e1 ih_e2 =>
    have h' := h.2.symm; subst h'; exact WellTyped.mul e1 e2 ih_e1 ih_e2
  case eq e1 e2 ih_e1 ih_e2 =>
    have h' := h.2.symm; subst h'
    match hty : e1.ty with
    | some .num => have hty' := h.1.1.symm; rw [hty] at hty'; exact WellTyped.eq e1 e2 .num (ih_e1 hty') (ih_e2 hty')
    | some .bool => have hty' := h.1.1.symm; rw [hty] at hty'; exact WellTyped.eq e1 e2 .bool (ih_e1 hty') (ih_e2 hty')
    | none => rw [hty] at h; have hc := h.1.2; simp [Option.isSome] at hc
  case lt e1 e2 ih_e1 ih_e2 =>
    have h' := h.2.symm; subst h'; exact WellTyped.lt e1 e2 ih_e1 ih_e2
  case gt e1 e2 ih_e1 ih_e2 =>
    have h' := h.2.symm; subst h'; exact WellTyped.gt e1 e2 ih_e1 ih_e2
  case le e1 e2 ih_e1 ih_e2 =>
    have h' := h.2.symm; subst h'; exact WellTyped.le e1 e2 ih_e1 ih_e2
  case ge e1 e2 ih_e1 ih_e2 =>
    have h' := h.2.symm; subst h'; exact WellTyped.ge e1 e2 ih_e1 ih_e2
  case and e1 e2 ih_e1 ih_e2 =>
    have h' := h.2.symm; subst h'; exact WellTyped.and e1 e2 ih_e1 ih_e2
  case or e1 e2 ih_e1 ih_e2 =>
    have h' := h.2.symm; subst h'; exact WellTyped.or e1 e2 ih_e1 ih_e2

theorem WellTyped.ty {e ty} : WellTyped e ty ↔ e.ty = some ty :=
 ⟨fun h => ty_some h, fun h => some_ty h⟩

def Expr.isBool (e : Expr) : Prop := e.ty = some .bool
def Expr.isNum (e : Expr) : Prop := e.ty = some .num

theorem Expr.isBool_iff_well_typed (e : Expr) : e.isBool ↔ WellTyped e .bool := by
  simp [isBool]
  rw [WellTyped.ty]

theorem Expr.isNum_iff_well_typed (e : Expr) : e.isNum ↔ WellTyped e .num := by
  simp [isNum]
  rw [WellTyped.ty]

end While
