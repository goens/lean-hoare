import Hoare.While

namespace Hoare

structure Triple where
  (P : Context → Prop)
  (c : While.Com)
  (Q : Context → Prop)

syntax "{" term "}" com "{" term "}" : term
macro_rules
| `({ $P } $c:com { $Q }) => `(Triple.mk $P [com| $c] $Q)

#check { fun _ => True } X := 4 { fun _ => True }

end Hoare
