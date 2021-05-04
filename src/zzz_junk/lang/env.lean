import .var

structure env :=
(bool_var_interp : var bool → bool)
(nat_var_interp : var nat → nat)

-- Collect init environments for each of the supported types
def init_env [a: has_var bool] [b: has_var nat] : env :=
  ⟨ a.init, b.init ⟩ 
