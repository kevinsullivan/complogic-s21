import .env
import .arith_expr

/-
inductive bool_var : Type
| mk (n : nat)
-/
abbreviation bool_var := var bool 


/-
Abstract syntax
-/
inductive bool_expr : Type
| lit_expr : bool → bool_expr 
| var_expr : bool_var → bool_expr
| and_expr : bool_expr → bool_expr → bool_expr 
| or_expr : bool_expr → bool_expr → bool_expr 
| impl_expr : bool_expr → bool_expr → bool_expr   
| not_expr : bool_expr → bool_expr
| le_expr : arith_expr → arith_expr -> bool_expr  -- Exam
| eq_expr : arith_expr → arith_expr -> bool_expr  -- Exam

open bool_expr 

/-
Concrete syntax
-/
notation e1 ∧ e2 := and_expr e1 e2
notation e1 ∨ e2 := or_expr e1 e2
notation ¬e := not_expr e
notation `[` b `]` := lit_expr b
notation `[` v `]` := var_expr v
reserve infixr `=>`:67              
notation e1 => e2 := impl_expr e1 e2   
notation a1 <= a2 := le_expr a1 a2      -- Exam
notation a1 == a2 := eq_expr a1 a2      -- Exan

/-
Semantics
-/

-- Boolean implies function, not provided by Lean
def bimp : bool → bool → bool 
| tt ff := ff
| _ _ := tt


def eql : ℕ → ℕ → bool      -- EXAM
| 0 0 := tt
| 0 _ := ff
| _ 0 := ff
|(n'+1)(m'+1):= eq n' m'


def le : ℕ → ℕ → bool       -- EXAM
| 0 _ := tt
| _ 0 := ff
| (n'+1)(m'+1) := le n' m'


--def bool_eval : bool_expr → (bool_var → bool) → bool
def bool_eval : bool_expr → env → bool
| (lit_expr b) _ := b
| (var_expr v) st := st.bool_var_interp v 
| (and_expr e1 e2) st := band (bool_eval e1 st) (bool_eval e2 st)
| (or_expr e1 e2) st := bor (bool_eval e1 st) (bool_eval e2 st)
| (impl_expr e1 e2) st := bimp (bool_eval e1 st) (bool_eval e2 st) 
| (not_expr e) st := bnot (bool_eval e st)
-- Exam 
| (le_expr a1 a2) st := le (arith_expr_eval st a1) (arith_expr_eval st a2)
| (eq_expr a1 a2) st := eql (arith_expr_eval st a1) (arith_expr_eval st a2)

-- Provide initial values/interpretation for variables of type (var nat)
instance : has_var bool := ⟨ λ (v : var bool), ff ⟩   

-- Override the value of a Boolean variable, returning an updated env
def override_bool : env → var bool → bool_expr → env
| (env.mk bi ni) v expr := 
⟨ 
  λ (v' : var bool), 
    if (var_eq v v') 
    then (bool_eval expr (env.mk bi ni)) 
    else (bi v'),
  ni
⟩ 

