import Hoare.While.Syntax
import Hoare.While.Context
import Hoare.While.Types

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
  | Expr.le e1 e2 => match e1.val? Γ, e2.val? Γ with
    | some (Val.num n1), some (Val.num n2) => some (Val.bool (n1 ≤ n2))
    | _, _ => none
  | Expr.ge e1 e2 => match e1.val? Γ, e2.val? Γ with
    | some (Val.num n1), some (Val.num n2) => some (Val.bool (n1 ≥ n2))
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

syntax ident "⊢" " 〚" bexpr "〛" : term
syntax "〚" com "〛" : term
macro_rules
| `($Γ:ident ⊢ 〚$e:bexpr〛) => `(Expr.val? $Γ [bexpr| $e] )
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

def Val.ty : Val → Ty
  | num _ => .num
  | bool _ => .bool

def Expr.val_ty (e : Expr) (t : Ty) : Prop :=
  ∀ Γ, ∀ val, (e.val? Γ = .some val) → val.ty = t

theorem Expr.val_add {e₁ e₂ : Expr} {val : Val} {Γ : Context} :
   (Expr.add e₁ e₂).val? Γ = val →
  ∃ n₁ n₂, e₁.val? Γ = Val.num n₁ ∧ e₂.val? Γ = Val.num n₂ ∧ val = Val.num (n₁ + n₂) := by
  intro h
  simp [val?] at h
  split at h
  · case h_1 x1 x2 n1 n2 heq1 heq2 =>
      exists n1; exists n2
      exact ⟨heq1, ⟨heq2, Option.some_inj.1 h |>.symm⟩⟩
  · case h_2 x1 x2 hx =>
      contradiction

theorem Expr.val_sub {e₁ e₂ : Expr} {val : Val} {Γ : Context} :
   (Expr.sub e₁ e₂).val? Γ = val →
  ∃ n₁ n₂, e₁.val? Γ = Val.num n₁ ∧ e₂.val? Γ = Val.num n₂ ∧ val = Val.num (n₁ - n₂) := by
  intro h
  simp [val?] at h
  split at h
  · case h_1 x1 x2 n1 n2 heq1 heq2 =>
      exists n1; exists n2
      exact ⟨heq1, ⟨heq2, Option.some_inj.1 h |>.symm⟩⟩
  · case h_2 x1 x2 hx =>
      contradiction

theorem Expr.val_mul {e₁ e₂ : Expr} {val : Val} {Γ : Context} :
   (Expr.mul e₁ e₂).val? Γ = val →
  ∃ n₁ n₂, e₁.val? Γ = Val.num n₁ ∧ e₂.val? Γ = Val.num n₂ ∧ val = Val.num (n₁ * n₂) := by
  intro h
  simp [val?] at h
  split at h
  · case h_1 x1 x2 n1 n2 heq1 heq2 =>
      exists n1; exists n2
      exact ⟨heq1, ⟨heq2, Option.some_inj.1 h |>.symm⟩⟩
  · case h_2 x1 x2 hx =>
      contradiction

theorem Expr.val_eq {e₁ e₂ : Expr} {val : Val} {Γ : Context} :
   (Expr.eq e₁ e₂).val? Γ = val →
  (∃ n₁ n₂, e₁.val? Γ = Val.num n₁ ∧ e₂.val? Γ = Val.num n₂ ∧ val = Val.bool (n₁ == n₂)) ∨
  (∃ b₁ b₂, e₁.val? Γ = Val.bool b₁ ∧ e₂.val? Γ = Val.bool b₂ ∧ val = Val.bool (b₁ == b₂)) := by
  intro h
  simp [val?] at h
  split at h
  · case h_1 x1 x2 n1 n2 heq1 heq2 =>
      left; exists n1; exists n2
      exact ⟨heq1, ⟨heq2, Option.some_inj.1 h |>.symm⟩⟩
  · case h_2 x1 x2 b1 b2 heq1 heq2 =>
      right; exists b1; exists b2
      exact ⟨heq1, ⟨heq2, Option.some_inj.1 h |>.symm⟩⟩
  · case h_3 x1 x2 hx =>
      contradiction

theorem Expr.val_lt {e₁ e₂ : Expr} {val : Val} {Γ : Context} :
   (Expr.lt e₁ e₂).val? Γ = val →
  ∃ n₁ n₂, e₁.val? Γ = Val.num n₁ ∧ e₂.val? Γ = Val.num n₂ ∧ val = Val.bool (n₁ < n₂) := by
  intro h
  simp [val?] at h
  split at h
  · case h_1 x1 x2 n1 n2 heq1 heq2 =>
      exists n1; exists n2
      exact ⟨heq1, ⟨heq2, Option.some_inj.1 h |>.symm⟩⟩
  · case h_2 x1 x2 hx =>
      contradiction

theorem Expr.val_gt {e₁ e₂ : Expr} {val : Val} {Γ : Context} :
   (Expr.gt e₁ e₂).val? Γ = val →
  ∃ n₁ n₂, e₁.val? Γ = Val.num n₁ ∧ e₂.val? Γ = Val.num n₂ ∧ val = Val.bool (n₁ > n₂) := by
  intro h
  simp [val?] at h
  split at h
  · case h_1 x1 x2 n1 n2 heq1 heq2 =>
      exists n1; exists n2
      exact ⟨heq1, ⟨heq2, Option.some_inj.1 h |>.symm⟩⟩
  · case h_2 x1 x2 hx =>
      contradiction

theorem Expr.val_le {e₁ e₂ : Expr} {val : Val} {Γ : Context} :
   (Expr.le e₁ e₂).val? Γ = val →
  ∃ n₁ n₂, e₁.val? Γ = Val.num n₁ ∧ e₂.val? Γ = Val.num n₂ ∧ val = Val.bool (n₁ ≤ n₂) := by
  intro h
  simp [val?] at h
  split at h
  · case h_1 x1 x2 n1 n2 heq1 heq2 =>
      exists n1; exists n2
      exact ⟨heq1, ⟨heq2, Option.some_inj.1 h |>.symm⟩⟩
  · case h_2 x1 x2 hx =>
      contradiction

theorem Expr.val_ge {e₁ e₂ : Expr} {val : Val} {Γ : Context} :
   (Expr.ge e₁ e₂).val? Γ = val →
  ∃ n₁ n₂, e₁.val? Γ = Val.num n₁ ∧ e₂.val? Γ = Val.num n₂ ∧ val = Val.bool (n₁ ≥ n₂) := by
  intro h
  simp [val?] at h
  split at h
  · case h_1 x1 x2 n1 n2 heq1 heq2 =>
      exists n1; exists n2
      exact ⟨heq1, ⟨heq2, Option.some_inj.1 h |>.symm⟩⟩
  · case h_2 x1 x2 hx =>
      contradiction

theorem Expr.val_and {e₁ e₂ : Expr} {val : Val} {Γ : Context} :
   (Expr.and e₁ e₂).val? Γ = val →
  ∃ b₁ b₂, e₁.val? Γ = Val.bool b₁ ∧ e₂.val? Γ = Val.bool b₂ ∧ val = Val.bool (b₁ && b₂) := by
  intro h
  simp [val?] at h
  split at h
  · case h_1 x1 x2 n1 n2 heq1 heq2 =>
      exists n1; exists n2
      exact ⟨heq1, ⟨heq2, Option.some_inj.1 h |>.symm⟩⟩
  · case h_2 x1 x2 hx =>
      contradiction

theorem Expr.val_or {e₁ e₂ : Expr} {val : Val} {Γ : Context} :
   (Expr.or e₁ e₂).val? Γ = val →
  ∃ b₁ b₂, e₁.val? Γ = Val.bool b₁ ∧ e₂.val? Γ = Val.bool b₂ ∧ val = Val.bool (b₁ || b₂) := by
  intro h
  simp [val?] at h
  split at h
  · case h_1 x1 x2 n1 n2 heq1 heq2 =>
      exists n1; exists n2
      exact ⟨heq1, ⟨heq2, Option.some_inj.1 h |>.symm⟩⟩
  · case h_2 x1 x2 hx =>
      contradiction

theorem Expr.var_not_val_ty (s) : ∀ t : Ty, ¬ (Expr.var s).val_ty t := by
  intro t hcontra
  cases t
  · case num =>
      simp [val_ty] at hcontra
      let v' : Val := Val.bool «true»
      let Γ : Context := [(s,v')]
      specialize hcontra Γ v'
      simp [val?, Context.getVal?, Γ, v', Val.ty] at hcontra
  · case bool =>
      simp [val_ty] at hcontra
      let v' : Val := Val.num 0
      let Γ : Context := [(s,v')]
      specialize hcontra Γ v'
      simp [val?, Context.getVal?, Γ, v', Val.ty] at hcontra

theorem Expr.well_typed_val {t : Ty} {e : Expr} : WellTyped e t ↔ e.val_ty t := by
  constructor
  · case mp =>
      intro h Γ val hval
      have hval := hval.symm
      have ht := WellTyped.ty_some h
      induction e generalizing val
      · case num => simp [Expr.ty] at ht; simp [val?] at hval; subst ht; subst hval; simp [Val.ty]
      · case bool => simp [Expr.ty] at ht; simp [val?] at hval; subst ht; subst hval; simp [Val.ty]
      · case var => simp [Expr.ty] at ht
      · case add e₁ e₂ ihe₁ ihe₂ ihv =>
          cases h
          case add ihwt₁ ihwt₂ =>
            simp [val?] at ihv
            have ⟨n1, n2, ⟨hn₁, hn₂, hnval⟩⟩ := Expr.val_add hval.symm
            rw [hnval]
            simp [Val.ty]
      · case sub e₁ e₂ ihe₁ ihe₂ ihv =>
          cases h
          case sub ihwt₁ ihwt₂ =>
            simp [val?] at ihv
            have ⟨n1, n2, ⟨hn₁, hn₂, hnval⟩⟩ := Expr.val_sub hval.symm
            rw [hnval]
            simp [Val.ty]
      · case mul e₁ e₂ ihe₁ ihe₂ ihv =>
          cases h
          case mul ihwt₁ ihwt₂ =>
            simp [val?] at ihv
            have ⟨n1, n2, ⟨hn₁, hn₂, hnval⟩⟩ := Expr.val_mul hval.symm
            rw [hnval]
            simp [Val.ty]
      · case eq e₁ e₂ ihe₁ ihe₂ ihv =>
          cases h
          case eq ihwt₁ ihwt₂ =>
            simp [val?] at ihv
            cases Expr.val_eq hval.symm
            · case inl hexists =>
              have ⟨n1, n2, ⟨hn₁, hn₂, hnval⟩⟩ := hexists
              rw [hnval]
              simp [Val.ty]
            · case inr hexists =>
              have ⟨n1, n2, ⟨hn₁, hn₂, hnval⟩⟩ := hexists
              rw [hnval]
              simp [Val.ty]
      · case lt e₁ e₂ ihe₁ ihe₂ ihv =>
          cases h
          case lt ihwt₁ ihwt₂ =>
            simp [val?] at ihv
            cases Expr.val_lt hval.symm
            · case intro hexists =>
              have ⟨n1, ⟨hn₁, hn₂, hnval⟩⟩ := hexists
              rw [hnval]
              simp [Val.ty]
      · case gt e₁ e₂ ihe₁ ihe₂ ihv =>
          cases h
          case gt ihwt₁ ihwt₂ =>
            simp [val?] at ihv
            cases Expr.val_gt hval.symm
            · case intro hexists =>
              have ⟨n1, ⟨hn₁, hn₂, hnval⟩⟩ := hexists
              rw [hnval]
              simp [Val.ty]
      · case le e₁ e₂ ihe₁ ihe₂ ihv =>
          cases h
          case le ihwt₁ ihwt₂ =>
            simp [val?] at ihv
            cases Expr.val_le hval.symm
            · case intro hexists =>
              have ⟨n1, ⟨hn₁, hn₂, hnval⟩⟩ := hexists
              rw [hnval]
              simp [Val.ty]
      · case ge e₁ e₂ ihe₁ ihe₂ ihv =>
          cases h
          case ge ihwt₁ ihwt₂ =>
            simp [val?] at ihv
            cases Expr.val_ge hval.symm
            · case intro hexists =>
              have ⟨n1, ⟨hn₁, hn₂, hnval⟩⟩ := hexists
              rw [hnval]
              simp [Val.ty]
      · case and e₁ e₂ ihe₁ ihe₂ ihv =>
          cases h
          case and ihwt₁ ihwt₂ =>
            simp [val?] at ihv
            cases Expr.val_and hval.symm
            · case intro hexists =>
              have ⟨n1, ⟨hn₁, hn₂, hnval⟩⟩ := hexists
              rw [hnval]
              simp [Val.ty]
      · case or e₁ e₂ ihe₁ ihe₂ ihv =>
          cases h
          case or ihwt₁ ihwt₂ =>
            simp [val?] at ihv
            cases Expr.val_or hval.symm
            · case intro hexists =>
              have ⟨n1, ⟨hn₁, hn₂, hnval⟩⟩ := hexists
              rw [hnval]
              simp [Val.ty]
  · case mpr =>
      simp [val_ty]
      intro h
      induction e
      · case num _ =>
        simp [val?, Val.ty] at h
        rw [←h]
        apply WellTyped.num
      · case bool _ =>
        simp [val?, Val.ty] at h
        rw [←h]
        apply WellTyped.bool
      · case var v =>
         exfalso
         apply Expr.var_not_val_ty v t
         assumption
      · case add e₁ e₂ ih₁ ih₂ =>
        -- t has to be num
        cases t
        · case num =>
          sorry
        · case bool =>
          -- contradiction
          sorry
      all_goals sorry

end While
