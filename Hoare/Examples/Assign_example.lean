import Hoare.While
import Hoare.Logic
import Hoare.Statements

open Hoare While



def foo : Triple :=
{(X + 1) == 2}
X := X + 1
{X == 2}

-- Here we use TripleHolds.assign' I had some inference problems getting TripleHolds.assign
-- to work.
theorem foo_holds' : TripleHolds foo := by
  let foo_stmt := foo.3
  let foo_com := foo.2
  let foo_expr := [expr| X + 1]
  apply TripleHolds.assign' foo_stmt foo_expr "X" foo_com

