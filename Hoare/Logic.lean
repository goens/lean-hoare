import Hoare.Basic

namespace Hoare

open While

-- TODO: define substitution properly
axiom _root_.Statement.subst :  String → Expr → Statement → Statement

inductive TripleHolds : Triple → Prop
  | skip {P : Statement} {c : Com} : TripleHolds {$(P)} $(c) {$(P)} --{P:= P, c := Com.skip, Q := P}
  | assign {P : Statement} {e : Expr} {x : String} {c : Com} : TripleHolds {$(P)} $(c) {$(P.subst x e)}
  | seq {P Q R : Statement} {c₁ c₂ : Com} :
      TripleHolds {$(P)} $(c₁) {$(Q)} → TripleHolds {$(Q)} $(c₂) {$(R)} →
      TripleHolds {$(P)} $(c₁);$(c₂) {$(Q)}
  | conditional {P Q : Statement} {B : Expr} {c₁ c₂ : Com}:
      TripleHolds {$(P) ∧ $(.atom B)} $(c₁) {$(Q)} → TripleHolds {$(P) ∧ ¬$(.atom B)} $(c₂) {$(Q)} →
      TripleHolds {$(P)} if $(B) then $(c₁) else $(c₂) fi {$(Q)}
  | while {P : Statement} {B : Expr} {c : Com}:
      TripleHolds {$(P) ∧ $(.atom B)} $(c) {$(Q)} →
      TripleHolds {$(P)} while $(B) do $(c) od {$(P) ∧ ¬$(.atom B)}
  | impl {P₁ P₂ Q₁ Q₂ : Statement} {c : Com}:
      (∀ Γ, P₁.eval Γ → P₂.eval Γ) → (∀ Γ, Q₂.eval Γ → Q₁.eval Γ) →
      TripleHolds {$(P₂)} $(c) {$(Q₂)} → TripleHolds {$(P₁)} $(c) {$(Q₁)}
