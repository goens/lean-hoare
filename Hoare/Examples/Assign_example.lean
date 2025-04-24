import Hoare.While
import Hoare.Logic
import Hoare.Statements

open Hoare While



def foo : Triple :=
{(X + 1) == 2}
X := X + 1
{X == 2}

def foo_com : Com := [com| X := X + 1]

def foo_expr : Expr := [expr| X + 1]

def foo_stmt : Statement := Statement.atom [expr| X == 2]

theorem foo_match  : Statement.subst "X" foo_expr foo_stmt = [stmt| (X + 1) == 2] := by
  simp [foo_expr, foo_stmt, Statement.subst]
  simp [Expr.subst]

-- Here we use TripleHolds.assign' I had some inference problems getting TripleHolds.assign
-- to work.
theorem foo_holds' : TripleHolds foo := by
  have := TripleHolds.assign' foo_stmt foo_expr "X" foo_com
  exact this
