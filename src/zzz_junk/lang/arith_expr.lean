import .env

-- Abstract syntax of arithmetic expressions
inductive arith_expr : Type 
| lit_arith_expr (n : nat)
| var_arith_expr (v : var nat)
| add_arith_expr (e1 e2 : arith_expr)
| mul_arith_expr (e1 e2 : arith_expr)

open arith_expr
universe u 

--def arith_expr_eval : var_state nat → arith_expr  → nat 
def arith_expr_eval : env → arith_expr  → nat
| st (lit_arith_expr n) := n
| st (var_arith_expr v) :=  st.nat_var_interp v
| st (add_arith_expr e1 e2) := (arith_expr_eval st e1) + (arith_expr_eval st e2)
| st (mul_arith_expr e1 e2) := (arith_expr_eval st e1) * (arith_expr_eval st e2)

notation `[` n `]` := lit_arith_expr n
notation `[` v `]` := var_arith_expr v
notation e1 + e2 := add_arith_expr e1 e2
notation e1 * e2 := mul_arith_expr e1 e2

-- Provide initial values/interpretation for variables of type (var nat)
instance : has_var nat := ⟨ λ (v : var nat), 0 ⟩   

-- Override the value of an arithmetic variable, returning an updated env
def override_nat : env → var nat → arith_expr → env
| (env.mk bi ni) v expr := 
  ⟨ bi,
    λ (v' : var nat), 
      if (var_eq v v') 
      then (arith_expr_eval (env.mk bi ni) expr) 
      else (ni v')
  ⟩ 
