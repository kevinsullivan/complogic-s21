/-
Propositions as types: the very idea.
-/

/-
Prop        Sort 0
Type 0      Sort 1
Type 1      Sort 2
Type 2      Sort 3       
...         ...
-/

/-
Idea #1. Use types to represent
logical propositions and values of
these types to represent "evidence" 
or "proofs" of truth. A type that
is inhabited we then judge to be
logically true, and one that is 
uninhabited we judge to be false. 
-/

/-
Idea #2. When we use values of a
type only to represent evidence
of logical truth, then it doesn't
really matter *which* value of a
type we pick as evidence. To the 
first order, we don't care which
proof of a theorem a mathematician
produces, only that there is at
least one. And indeed, any proof
will do to justify a judgment that
a proposition is true. So when we
represent propositions as types and
proofs as values, in some sense we
want every proof of a given type to
be equivalent to any other. We want
every value of a "logical" type to
be equivalent to any other. Making
this equivalence of proof terms is
one of the main purposes of the last
of Lean's type universes, which we 
now introduce: Prop. 
-/

inductive its_raining : Prop
| i_see_rain_falling : its_raining
| i_hear_rain_on_roof : its_raining

inductive streets_wet : Prop
| i_see_wet_streets : streets_wet
| i_feel_wet_streets : streets_wet

open its_raining streets_wet

def proof_1'' : its_raining := _
def proof_2'' : its_raining := _

lemma proof_1' : its_raining := _
lemma proof_2' : its_raining := _

theorem proof_1 : its_raining := _
theorem proof_2 : its_raining := _

/-
We just don't care which value of a
propositional type is used. When we 
see *equality* we'll find that values
build by different constructors in 
Sort n, for n > 0, are always NOT
equal, whereas all values of a type
in Sort 0, or Prop, are deemed equal.
Because different proof terms are
equivalent, they carry no information
beyond being evidence of truth. This
is the principle of proof irrelevance.
-/

/-
Just as we can represent propositions
as types, we can represent *predicates*
as type families, i.e., propositions
with parameters.
-/

inductive day : Type 
| su | mo | tu | we | th | fr | sa 

open day

/-
A type family indexed by day representing
the predicate ⟨ always_rains_on d ⟩, where
d is a parameter of type day. Providing a
value for d yields a specific proposition
in the family of propositions we've defined, 
namely one claims that a specific day, d, is
always rainy. 
-/
inductive always_rains_on : day → Prop
| mo_rainy : ∀ (d : day), (d = mo) → always_rains_on d

open always_rains_on

#check always_rains_on
#check always_rains_on su
#check always_rains_on mo
#check always_rains_on tu



lemma bad_tuesdays : always_rains_on tu := _  -- stuck
lemma bad_fridays : always_rains_on tu := _   -- stuck
lemma bad_mondays : always_rains_on mo := mo_rainy mo _

