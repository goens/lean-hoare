import Hoare.While
import Hoare.Logic

open Hoare While

def sqrt : Com := [com|
  S := 0;
  while ((S + 1) * (S + 1)) <= X do
    S := S + 1
  od
  ]

#eval sqrt.eval [X ↦ 36]c


-- def sqrt_spec (x : Nat) : Triple := {X == $(x) ∧ X >= 0} $(sqrt)  {X == $(x) ∧ S * S == X }

def sqrt_spec (x : Nat) : Triple :=
  {X == $(x) ∧ X >= 0}
  S := 0;
  while ((S + 1) * (S + 1)) <= X do
    S := S + 1
  od
  {X == $(x) ∧ S * S == X }

theorem sqrt_spec_holds : ∀ x, TripleHolds (sqrt_spec x) := by
  simp [sqrt_spec]
  sorry
