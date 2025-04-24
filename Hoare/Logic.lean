import Hoare.Basic

namespace Hoare

open While

-- TODO: define substitution properly
--axiom _root_.Statement.subst :  String → Expr → Statement → Statement

-- Not really sure if this is capture-avoiding subsitution, it was the most
-- naive thing to try. 

def Expr.subst (x : String) (e : Expr) (e' : Expr) : Expr :=
  match e' with
  | Expr.var y => if x == y then e else e'
  | Expr.num n => Expr.num n
  | Expr.bool b => Expr.bool b
  | Expr.add e1 e2 => Expr.add (Expr.subst x e e1) (Expr.subst x e e2)
  | Expr.sub e1 e2 => Expr.sub (Expr.subst x e e1) (Expr.subst x e e2)
  | Expr.mul e1 e2 => Expr.mul (Expr.subst x e e1) (Expr.subst x e e2)
  | Expr.eq e1 e2 => Expr.eq (Expr.subst x e e1) (Expr.subst x e e2)
  | Expr.lt e1 e2 => Expr.lt (Expr.subst x e e1) (Expr.subst x e e2)
  | Expr.gt e1 e2 => Expr.gt (Expr.subst x e e1) (Expr.subst x e e2)
  | Expr.le e1 e2 => Expr.le (Expr.subst x e e1) (Expr.subst x e e2)
  | Expr.ge e1 e2 => Expr.ge (Expr.subst x e e1) (Expr.subst x e e2)
  | Expr.and e1 e2 => Expr.and (Expr.subst x e e1) (Expr.subst x e e2)
  | Expr.or e1 e2 => Expr.or (Expr.subst x e e1) (Expr.subst x e e2)

def Statement.subst (x : String) (e : Expr) (P : Statement) : Statement :=
  match P with
  | Statement.atom expr => Statement.atom (Expr.subst x e expr)
  | Statement.conj P₁ P₂ => Statement.conj (Statement.subst x e P₁) (Statement.subst x e P₂)
  | Statement.disj P₁ P₂ => Statement.disj (Statement.subst x e P₁) (Statement.subst x e P₂)
  | Statement.neg P' => Statement.neg (Statement.subst x e P')
  | Statement.impl P₁ P₂ => Statement.impl (Statement.subst x e P₁) (Statement.subst x e P₂)
  | Statement.equiv P₁ P₂ => Statement.equiv (Statement.subst x e P₁) (Statement.subst x e P₂)

inductive TripleHolds : Triple → Prop
  | skip {P : Statement} {c : Com} : TripleHolds {$(P)} $(c) {$(P)} --{P:= P, c := Com.skip, Q := P}
  | assign {P : Statement} {e : Expr} {x : String} {c : Com} : TripleHolds {$(Statement.subst x e P)} $(c) {$(P)}
  -- for some reason I had a lot of inference problems with assign using curly braces,
  -- so I have added assign' which makes all parameters explicit and with assign prime I am
  -- able to prove hoare triple statment in Assign_example.lean
  | assign' (P : Statement) (e : Expr) (x : String) (c : Com) : TripleHolds {$(Statement.subst x e P)} $(c) {$(P)}
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
