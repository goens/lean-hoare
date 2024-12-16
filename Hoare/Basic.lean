import Hoare.While
import Hoare.Statements

namespace Hoare

structure Triple where
  (P : Statement)
  (c : While.Com)
  (Q : Statement)

syntax "{" stmt "}" com "{" stmt "}" : term
macro_rules
| `({ $P:stmt } $c:com { $Q:stmt }) => `(Triple.mk [stmt| $P] [com| $c] [stmt|$Q])

-- TODO: Delaborate identifiers, build functions for a natural notation for triples

#check { true } X := 4 { X > 4 }
#check fun (P Q : Statement) => { $(P) } X := 4 { $(Q) }


end Hoare
