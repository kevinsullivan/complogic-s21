import .assertion
import .imp
import .var_test

/-
Tests after completion of cmd syntax including if and while
-/

def p1 : cmd :=
IF (bool_expr.eq_expr [X] [2]) -- provide concrete syntax
THEN X = [1]
ELSE X = [2]

#eval (c_eval p1 init_env).2 X

/-
Fib
-/


/- 
Formal specification
-/
def fib : nat → nat 
| 0 := 1
| 1 := 1
| (n' + 2) := fib n' + fib (n' + 1) 

#eval fib 5

/-
Efficient implementation
-/


/-
pre: anything goes
{
  def fib(n) {
  fib0 = 1
  fib1 = 1
  if (n == 0) return fib0
  else if (n = 1) then fib1
  else
  index = 2;
  
  while (n > index) do
    fib0 = fib1
    fib1 = fib2
    acc = fib0 + fib 1
   index = index + 1
  end
  return acc;
}
post: retval = fib n
}
-/

def n  : var nat := var.mk 0
def fib0  : var nat := var.mk 1
def fib1 : var nat := var.mk 2
def accm : var nat := var.mk 3
def index: var nat := var.mk 4

-- assume input is in n
def fib_imp : cmd :=
n = [5];
-- is
fib0 = [1];
-- is
fib1 = [1];
-- is 
IF (bool_expr.eq_expr [n] [0])
THEN accm = [fib0]
ELSE IF (bool_expr.eq_expr [n] [1])
THEN accm = [fib1]
ELSE 
(
  index = [2];
  accm = [fib0] + [fib1];
  WHILE (bool_expr.le_expr [index] [n] ∧ ¬ bool_expr.eq_expr [index] [n]) 
  DO 
    (fib0 = [fib1];
    fib1 = [accm];
    accm = [fib0] + [fib1];
    index = [index] + [1])
  END
)

#eval (c_eval fib_imp init_env).2 accm


-- ∀ n, if we run fib_imp n then we always get the same answer that fib n will produce
-- true {fib_imp} accm = fib n


/-
n = 5
fib0 = 1
fib1 = 2
acc = 3
n = 3
fib0 = 2
fib1 = 3
acc = 5
n = 4
fib0 = 3
fib1 = 5
acc = 8
n = 5
return 8
-/




/-
Tests before completion of cmd syntax including if and while
-/


-- a little program: X gets overwritten
def program : cmd := 
  X = [7];
  Y = [8];
  Z = [9];
  X = [10]

-- verify that post state is as expected
def post_env := c_eval program init_env 
example : post_env.nat_var_interp X = 10 := rfl
example : post_env.nat_var_interp Y = 8 := rfl
example : post_env.nat_var_interp Z = 9 := rfl

open cmd

def p2 : cmd := IF [tt] THEN (program) ELSE (X=[2]) 
def p3 : cmd := IF [ff] THEN (X=[1]) ELSE (X=[2]) 

example : (c_eval p2 init_env).nat_var_interp X = 10 := rfl
example : (c_eval p3 init_env).nat_var_interp X = 2 := rfl

/-
Claim and prove logically that in "program" 
post state, X = 10.
-/
  theorem t1 : 
    ∀ (post : env), 
    c_sem program init_env post → 
    post.nat_var_interp X = 10 := 
  begin
    assume post,
    assume h,
    cases h,
    cases h_ᾰ_1,
    rw <- h_ᾰ_1_ᾰ,
    cases h_is,
    apply rfl,
  end

-- Exam: fix this proof
  example : 
    ∀ (post : env), c_sem program init_env post → post.nat_var_interp Z = 9 := 
  begin
    assume post,
    assume h,
    unfold program at h,
    cases h,
    cases h_ᾰ,
    cases h_ᾰ_ᾰ_1,
    cases h_ᾰ_1,
    rw <- h_ᾰ_1_ᾰ,
    rw <- h_ᾰ_ᾰ_1_ᾰ,
    unfold Z,
    apply rfl,      -- YOU FIX
  end


-- computational testing
example : (c_eval p2 init_env).nat_var_interp X = 1 := rfl  -- no
example : (c_eval p3 init_env).nat_var_interp X = 2 := rfl  -- yes

-- logical verification

example : 
  ∀ (e e' : env), c_sem p2 e e' → e'.nat_var_interp X = 1 :=
begin
  unfold p2,
  intros,
  cases ᾰ,
  cases ᾰ_ᾰ,  -- impossible case
  cases ᾰ_ᾰ_1,
  rw <- ᾰ_ᾰ_1_ᾰ,
  cases e,
  exact rfl,
end

