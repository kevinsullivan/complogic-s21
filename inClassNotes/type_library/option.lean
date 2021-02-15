#print option

namespace hidden

/-
Every function in Lean must be total.
That is, there has to be an answer for
*all* values of the argument type. We
will discuss the reason later in the
course, but for now you can believe
there's a good reason.

This constraint presents a problem if
we want to represent *partial* functions
in constructive logic, i.e., functions
that are not defined for all values of 
its argument type(s).

Examples: 

    Total function from bool to bool
    tt --> 1
    ff --> 0

    Partial function from bool to bool
    tt --> 1
    ff ---> 

Indeed, Π means "for *every* value" of
one type there is *some* corresponding
value of another type. Check it out.
-/

#check ℕ → ℕ 
#check Π (n : nat), nat
#check ∀ (n : nat), nat

/-
All three expresions express the
type of *total* functions from ℕ
to ℕ. The arrow notation is just 
a nice, conventional, shorthand.

Suppose for example we want to 
represent a partial function from 
bool to nat that returns one if a 
given bool argument is bool.tt 
and that is otherwise undefined.

We can represent this *partial* 
function as a *total* function 
from bool to the type, option nat.
An option type is a simple sum of 
products type, with two variants. 
The "none" variant (constructor) 
represents "undefined, while the
"some a" variant boxes a value 
(a : α) representing the defined
value of a function for a given
argument.

Here's a polymorphic option type. 
-/

universe u 

inductive option (α : Type u) : Type u
| none : option
| some (a : α) : option

end hidden