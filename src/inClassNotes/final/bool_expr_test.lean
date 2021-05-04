import .bool_expr 
import .arith_expr
import .var_test


-- create a few expressions
def true_expr : bool_expr := [tt]
def false_expr : bool_expr := [ff]
def e1 := [tt] ∧ [ff]
def e2 := e1 ∨  [tt]

-- create variable expressions
-- see notations in bool_expr
def e3 := [P] ∧ ¬[P]
def e4 := [P] ∨ ¬[P]
def e5 := [P] => ¬[R]

-- Get an initial environment
def init : env := init_env

-- Evaluate expressions in it (haha)
#eval bool_eval e1 init 
#eval bool_eval e2 init 
#eval bool_eval e3 init 
#eval bool_eval e4 init 
#eval bool_eval e5 init 

#eval le 3 7

-- Finally a Boolean expression with embedded arithmetic
                                      -- FIX THE FOLLOWING
#reduce arith_expr_eval init [3]      -- Inconsistent arg order conventions 
#reduce bool_eval ([3] <= [4]) init   -- Fix it, with exprs before envs