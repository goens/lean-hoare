import Hoare.While.Syntax
import Hoare.While.Types
import Hoare.While.OperationalSemantics
import Hoare.While.DenotationalSemantics

inductive Statement
  | atom : While.Expr → Statement
  | disj : Statement → Statement → Statement
  | conj : Statement → Statement → Statement
  | neg : Statement → Statement
  | impl : Statement → Statement → Statement
  | equiv : Statement → Statement → Statement

declare_syntax_cat stmt
syntax expr : stmt
syntax stmt " ∧ " stmt : stmt
syntax stmt " ∨ " stmt : stmt
syntax "¬" stmt : stmt
syntax stmt " ⇒ " stmt : stmt
syntax stmt " ⇔ " stmt : stmt
syntax "[stmt|" stmt "]" : term

macro_rules
  | `([stmt| $x:expr]) => `(Statement.atom [expr|$x])
  | `([stmt| $x ∧ $y]) => `(Statement.conj [stmt|$x] [stmt|$y])
  | `([stmt| $x ∨ $y]) => `(Statement.disj [stmt|$x] [stmt|$y])
  | `([stmt| ¬ $x]) => `(Statement.neg [stmt|$x])
  | `([stmt| $x ⇒ $y]) => `(Statement.impl [stmt|$x] [stmt|$y])
  | `([stmt| $x ⇔ $y]) => `(Statement.equiv [stmt|$x] [stmt|$y])

def Statement.eval (Γ : While.Context) : Statement  → Prop
  | atom e => match e.val? Γ with
    | some (While.Val.bool b) => (b = .true)
    | _ => False
  | disj p q => p.eval Γ ∨ q.eval Γ
  | conj p q => p.eval Γ ∧ q.eval Γ
  | neg p => ¬ p.eval Γ
  | impl p q => p.eval Γ → q.eval Γ
  | equiv p q => p.eval Γ ↔ q.eval Γ

-- TODO: this must be golfable!
instance {Γ : While.Context} {e : While.Expr} : Decidable (Statement.eval Γ (Statement.atom e)) :=
   match While.decideVal? (Γ:=Γ) (e:=e) with
       | isTrue h => isTrue (by simp [Statement.eval, h])
       | isFalse h => isFalse <| by
         simp [Statement.eval]
         cases he : e.val? Γ
         · simp
         · case some v =>
            cases hv : v
            · case num _ => simp
            · case bool b =>
                cases hb : b
                · case «false» => simp
                · case «true» => rw [he, hv, hb] at h; simp_all

def Statement.decidable  (Γ  : While.Context) (s : Statement) : Decidable (Statement.eval Γ s) :=
   match s with
     | .atom e => inferInstance
     | .disj p q => match decidable Γ p with
       | isTrue h =>  isTrue (Or.inl h)
       | isFalse h => match decidable Γ q with
         | isTrue h' => isTrue (Or.inr h')
         | isFalse h' => isFalse (by simp [Statement.eval, h, h'])
      | .conj p q => match decidable Γ p with
        | isTrue h => match decidable Γ q with
          | isTrue h' => isTrue ⟨h, h'⟩
          | isFalse h' => isFalse (by simp [Statement.eval, h, h'])
        | isFalse h => isFalse (by simp [Statement.eval, h])
      | .neg p => match decidable Γ p with
        | isTrue h => isFalse (by simp [Statement.eval, h])
        | isFalse h => isTrue (by simp [Statement.eval, h])
      | .impl p q => match decidable Γ p with
        | isTrue h => match decidable Γ q with
          | isTrue h' => isTrue (by simp [Statement.eval, h, h'])
          | isFalse h' => isFalse (by simp [Statement.eval, h, h'])
        | isFalse h => isTrue (by simp [Statement.eval, h])
      | .equiv p q => match decidable Γ p with
        | isTrue h => match decidable Γ q with
          | isTrue h' => isTrue (by simp [Statement.eval, h, h'])
          | isFalse h' => isFalse (by simp [Statement.eval, h, h'])
        | isFalse h => match decidable Γ q with
          | isTrue h' => isFalse (by simp [Statement.eval, h, h'])
          | isFalse h' => isTrue (by simp [Statement.eval, h, h'])

instance {s : Statement} {Γ  : While.Context} : Decidable (Statement.eval Γ s) := Statement.decidable Γ s
