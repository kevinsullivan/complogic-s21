#print nat

namespace hidden

/-
Here's Lean's definition of the
list type builder. We'll use it
instead of our own version.

universe u

inductive list (α : Type u) : Type u
| nil : list
| cons : α → list → list 
-/

#print list 

end hidden

