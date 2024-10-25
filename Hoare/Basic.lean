import Hoare.While

namespace Hoare

structure Triple where
  (P : Context → Prop)
  (c : While.Com)
  (Q : Context → Prop)

-- This should not be `term` but rather `statement` with restricted propositional fragment
syntax "{" term "}" com "{" term "}" : term
macro_rules
| `({ $P } $c:com { $Q }) => `(Triple.mk $P [com| $c] $Q)

-- TODO: Delaborate identifiers, build functions for a natural notation for triples

#check { fun _ => True } X := 4 { fun _ => True }

end Hoare
