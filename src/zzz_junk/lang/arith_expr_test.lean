import .bool_expr
import .var_test

example : 
  arith_expr_eval 
    init_env 
    ([3] + [5]) = 
  8 := 
  rfl 

example : 
  arith_expr_eval 
    init_env 
    ([3] + [5] + [@var.mk nat 0]) = 
  8 := 
  rfl 

def st := override_nat init_env X [7]
#eval st.nat_var_interp X
#eval st.nat_var_interp Y
#eval st.nat_var_interp Z

def st' := override_nat st Y [8]

#eval st'.nat_var_interp X
#eval st'.nat_var_interp Y
#eval st'.nat_var_interp Z

def st'' := override_nat st' Z [9]

#eval st''.nat_var_interp X
#eval st''.nat_var_interp Y
#eval st''.nat_var_interp Z
 

def st''' := override_nat st'' X [10]

#eval st'''.nat_var_interp X
#eval st'''.nat_var_interp Y
#eval st'''.nat_var_interp Z