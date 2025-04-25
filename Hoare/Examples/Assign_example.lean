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

def foo' : Triple :=
{(X + 1) == 2}
X := X + 2
{X == 2}

-- Now we can prove that `X := X + 2` also changes `X` from 1 to 2.
-- There's something funky happening here!
-- (See Logic.lean)
theorem foo'_holds : TripleHolds foo' := by
  let foo_stmt := foo'.3
  let foo_com := foo'.2
  let foo_expr := [expr| X + 1]
  apply TripleHolds.assign' foo_stmt foo_expr "X" foo_com


#reduce [stmt| X == 1].subst "X" [expr| X + 1]

-- This fails! There's another problem we have, namely that we're comparing syntactic equality of stmts, not their semantics.
example : [stmt| X == 1].subst "X" [expr| X + 1] = [stmt| X == 2] := by
  simp [Statement.subst, Expr.subst]

-- Ideally, this should "just" work for this to be realtively useful.
example : TripleHolds {X == 1} X := X + 1 {X == 2} := by
   apply TripleHolds.assign -- I would hope this shold "just work"
