import .assertion
import .arith_expr_test
import .bool_expr_test
import .var_test
import .imp_test


def pre1 : Assertion := 
  λ (e : env),
    (e.bool_var_interp P = tt) ∧ 
    (e.nat_var_interp X = 10)

/-
An assertion that's satisfied by any state
-/

def any : Assertion := λ (e : env), true

/-
Pre: X = 10 or Y = 8
-/

def pre2 : Assertion := λ (e : env), 
  e.nat_var_interp X = 10 ∨ e.nat_var_interp Y = 8


def res := c_eval program init_env 


example : pre2 res := 
begin
  unfold pre2,
  apply or.inr,
  apply rfl,
end


def prog2 := X = [10]

#check override_nat

lemma bar : satisfies prog2 any (λ st : env, st.nat_var_interp X = 10) :=
begin
  unfold satisfies,
  assume st st',
  assume trivial h,
  unfold prog2 at h,
  cases h,
  cases st, 
  unfold X,
  rw <- h_ᾰ,
  exact rfl,
end

example : ∀ (n m k : nat), m = n → k = m → n = k :=
begin 
  intros n m k,
  assume h1 h2,
  rw <- h1,
  rw h2,
end

example : any { prog2 } (λ st' : env, 
  st'.nat_var_interp X = 10 ∨ st'.nat_var_interp Y = 9) :=
begin
unfold satisfies, 
-- COMPLETE THIS PROOF
end











def a1 : cmd := X = [7]
def a2 := Y = [8]
def a3 := Z = [9]
def a4 := X = [10]

def program : cmd := -- a1; a2; a3; a4
  X = [7];
  Y = [8];
  Z = [9];
  X = [10]


