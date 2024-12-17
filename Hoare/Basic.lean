import Hoare.While
import Hoare.Statements

namespace Hoare

structure Triple where
  (P : Statement)
  (c : While.Com)
  (Q : Statement)

syntax "{" stmt "} " com " {" stmt "}" : term
macro_rules
| `({ $P:stmt } $c:com { $Q:stmt }) => `(Triple.mk [stmt| $P] [com| $c] [stmt|$Q])

-- TODO: Delaborate identifiers, build functions for a natural notation for triples
@[app_unexpander Hoare.Triple.mk]
def unexpandTriple : Lean.PrettyPrinter.Unexpander
  | `($_ [stmt| $p] [com| $c] [stmt| $q]) => `({$p} $c {$q})
  | `($_ [stmt| $p] $c:term [stmt| $q]) => `({$p} $($c) {$q})
  | `($_ $p:term $c:term [stmt| $q]) => `({$($p)} $($c) {$q})
  | `($_ $p:term [com| $c] $q:term) => `({$($p)} $c {$($q)})
  | _ => throw ()

#check { true } X := 4 { X > 4 }
#check fun (P Q : Statement) => { $(P) } X := 4 { $(Q) }


end Hoare
