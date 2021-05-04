/-
Implement a programmer-friendly interface
for looking up the value of variables with
values of different types: a typeclasses, 
has_vars (T : Type) := (init : var T -> T).
In other words, each type contributes an
instance, and thus a definition what what
environment to use as the init environment
for that type.
-/

universe u

/-
Variables for values of type α, indexed by nat
-/ 
structure var (α : Type u) : Type u := 
  (n : nat)


-- This work?
def var_eq {α : Type} : var α → var α → bool 
| (var.mk n1) (var.mk n2) := n1 = n2 


/-
The type of our state function for α-valued variables  
-/
def var_state (α : Type u) := 
  var α → α 

/-
An initial state value for each var-supporting type
Implement to enable eval evalation for values of var α
-/
class has_var (α : Type u) := 
  (init : var_state α)




