import Hoare.Statements

namespace While


def simplifyConstants : Expr → Expr
| Expr.add e1 e2 =>
    let s1 := simplifyConstants e1
    let s2 := simplifyConstants e2
    match s1, s2 with
    | Expr.num n1, Expr.num n2 => Expr.num (n1 + n2)
    | _, _ => Expr.add s1 s2
| Expr.sub e1 e2 =>
    let s1 := simplifyConstants e1
    let s2 := simplifyConstants e2
    match s1, s2 with
    | Expr.num n1, Expr.num n2 => Expr.num (n1 - n2)
    | _, _ => Expr.sub s1 s2
| Expr.mul e1 e2 =>
    let s1 := simplifyConstants e1
    let s2 := simplifyConstants e2
    match s1, s2 with
    | Expr.num n1, Expr.num n2 => Expr.num (n1 * n2)
    | _, _ => Expr.mul s1 s2
| Expr.var x => Expr.var x
| e => e


def normalizeEq (e1 e2 : Expr) : Expr :=
match e1, e2 with
| Expr.var x, e2 => Expr.eq (Expr.var x) (simplifyConstants e2)
| e2, Expr.var x => Expr.eq (Expr.var x) (simplifyConstants e2)
| Expr.add (Expr.var x) e, e2 => Expr.eq (Expr.var x) (simplifyConstants (Expr.sub e2 e))
| Expr.add e (Expr.var x), e2 => Expr.eq (Expr.var x) (simplifyConstants (Expr.sub e2 e))
| Expr.sub (Expr.var x) e, e2 => Expr.eq (Expr.var x) (simplifyConstants (Expr.add e2 e))
| Expr.sub e (Expr.var x), e2 => Expr.eq (Expr.var x) (simplifyConstants (Expr.sub e e2))
| _, _ => Expr.eq e1 e2

def normalizeGe (e1 e2 : Expr) : Expr :=
match e1, e2 with
| Expr.var x, e2 => Expr.ge (Expr.var x) (simplifyConstants e2)
| e2, Expr.var x => Expr.le (Expr.var x) (simplifyConstants e2)
| Expr.add (Expr.var x) e, e2 => Expr.ge (Expr.var x) (simplifyConstants (Expr.sub e2 e))
| Expr.add e (Expr.var x), e2 => Expr.ge (Expr.var x) (simplifyConstants (Expr.sub e2 e))
| Expr.sub (Expr.var x) e, e2 => Expr.ge (Expr.var x) (simplifyConstants (Expr.add e2 e))
| Expr.sub e (Expr.var x), e2 => Expr.ge (Expr.var x) (simplifyConstants (Expr.sub e e2))
| _, _ => Expr.ge e1 e2

def normalizeLe (e1 e2 : Expr) : Expr :=
match e1, e2 with
| Expr.var x, e2 => Expr.le (Expr.var x) (simplifyConstants e2)
| e2, Expr.var x => Expr.ge (Expr.var x) (simplifyConstants e2)
| Expr.add (Expr.var x) e, e2 => Expr.le (Expr.var x) (simplifyConstants (Expr.sub e2 e))
| Expr.add e (Expr.var x), e2 => Expr.le (Expr.var x) (simplifyConstants (Expr.sub e2 e))
| Expr.sub (Expr.var x) e, e2 => Expr.le (Expr.var x) (simplifyConstants (Expr.add e2 e))
| Expr.sub e (Expr.var x), e2 => Expr.le (Expr.var x) (simplifyConstants (Expr.sub e e2))
| _, _ => Expr.le e1 e2

def normalizeGt (e1 e2 : Expr) : Expr :=
match e1, e2 with
| Expr.var x, e2 => Expr.gt (Expr.var x) (simplifyConstants e2)
| e2, Expr.var x => Expr.lt (Expr.var x) (simplifyConstants e2)
| Expr.add (Expr.var x) e, e2 => Expr.gt (Expr.var x) (simplifyConstants (Expr.sub e2 e))
| Expr.add e (Expr.var x), e2 => Expr.gt (Expr.var x) (simplifyConstants (Expr.sub e2 e))
| Expr.sub (Expr.var x) e, e2 => Expr.gt (Expr.var x) (simplifyConstants (Expr.add e2 e))
| Expr.sub e (Expr.var x), e2 => Expr.gt (Expr.var x) (simplifyConstants (Expr.sub e e2))
| _, _ => Expr.gt e1 e2

def normalizeLt (e1 e2 : Expr) : Expr :=
match e1, e2 with
| Expr.var x, e2 => Expr.lt (Expr.var x) (simplifyConstants e2)
| e2, Expr.var x => Expr.gt (Expr.var x) (simplifyConstants e2)
| Expr.add (Expr.var x) e, e2 => Expr.lt (Expr.var x) (simplifyConstants (Expr.sub e2 e))
| Expr.add e (Expr.var x), e2 => Expr.lt (Expr.var x) (simplifyConstants (Expr.sub e2 e))
| Expr.sub (Expr.var x) e, e2 => Expr.lt (Expr.var x) (simplifyConstants (Expr.add e2 e))
| Expr.sub e (Expr.var x), e2 => Expr.lt (Expr.var x) (simplifyConstants (Expr.sub e e2))
| _, _ => Expr.lt e1 e2

def Expr.normalize : Expr → Expr
| Expr.eq e1 e2 => normalizeEq e1 e2
| Expr.add e1 e2 => Expr.add (Expr.normalize e1) (Expr.normalize e2)
| Expr.sub e1 e2 => Expr.sub (Expr.normalize e1) (Expr.normalize e2)
| Expr.mul e1 e2 => Expr.mul (Expr.normalize e1) (Expr.normalize e2)
| Expr.or e1 e2 => Expr.or (Expr.normalize e1) (Expr.normalize e2)
| Expr.and e1 e2 => Expr.and (Expr.normalize e1) (Expr.normalize e2)
| Expr.ge e1 e2 => normalizeGe (Expr.normalize e1) (Expr.normalize e2)
| Expr.le e1 e2 => normalizeLe (Expr.normalize e1) (Expr.normalize e2)
| Expr.gt e1 e2 => normalizeGt (Expr.normalize e1) (Expr.normalize e2)
| Expr.lt e1 e2 => normalizeLt (Expr.normalize e1) (Expr.normalize e2)
| Expr.var x => Expr.var x
| Expr.bool b => Expr.bool b
| Expr.num n => Expr.num n


def Statement.normalize : Statement → Statement
| Statement.atom e => Statement.atom (Expr.normalize e)
| Statement.conj s1 s2 => Statement.conj (Statement.normalize s1) (Statement.normalize s2)
| Statement.disj s1 s2 => Statement.disj (Statement.normalize s1) (Statement.normalize s2)
| Statement.neg s => Statement.neg (Statement.normalize s)
| Statement.impl s1 s2 => Statement.impl (Statement.normalize s1) (Statement.normalize s2)
| Statement.equiv s1 s2 => Statement.equiv (Statement.normalize s1) (Statement.normalize s2)



#eval Statement.normalize ([stmt|( x + 3) == 34 ])
#check [stmt| x + 1 == 2]


-- Before doing statements lets first try and do expressions

def Equiv.expressions (P Q : Expr) : Prop := ∀ (Γ : Context),
P.val? Γ = Q.val? Γ

-- Before even doing expressions fully I want to first understand what happens for simplifying constants
theorem simplifyConstants_preserves_eval (e : Expr) (Γ : Context) :
  Expr.val? Γ (simplifyConstants e) = Expr.val? Γ e := by
  induction e
  case add e₁ e₂ ih₁ ih₂ =>
    simp [simplifyConstants, Expr.val?]
    rw [← ih₁, ← ih₂]
    split
    · case h_1 s₁ s₂ n₁ n₂ hs₁ hs₂ =>
        simp [Expr.val?, hs₁, hs₂]
    · case h_2 s₁ s₂ hs =>
        simp [Expr.val?]
  case sub e₁ e₂ ih₁ ih₂ =>
    simp [simplifyConstants, Expr.val?]
    rw [← ih₁, ← ih₂]
    split
    · case h_1 s₁ s₂ n₁ n₂ hs₁ hs₂ =>
        simp [Expr.val?, hs₁, hs₂]
    · case h_2 s₁ s₂ hs =>
        simp [Expr.val?]
  case mul e₁ e₂ ih₁ ih₂ =>
    simp [simplifyConstants, Expr.val?]
    rw [← ih₁, ← ih₂]
    split
    · case h_1 s₁ s₂ n₁ n₂ hs₁ hs₂ =>
        simp [Expr.val?, hs₁, hs₂]
    · case h_2 s₁ s₂ hs =>
        simp [Expr.val?]
  all_goals simp [Expr.val?, simplifyConstants]


-- Now lets just try and understand what happens for x + e == e2 ---> x == e2 - e

 theorem NormalizeAdd (Γ : Context) (x : String) (e e2 : Expr) :
  Expr.val? Γ (Expr.eq (Expr.add (Expr.var x) e) e2) =
  Expr.val? Γ (normalizeEq (Expr.add (Expr.var x) e) e2) := by
  sorry

theorem NormalisEquiv (P : Expr) : Equiv.expressions (Expr.normalize P) P := by sorry
