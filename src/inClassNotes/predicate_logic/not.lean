/-
If P is a proposition, then so is ¬P.
We just ¬P to be true when P is false:
when there is no proof of it at all. 
-/

#check not

/-
def not (a : Prop) := a → false
prefix `¬` := not
-/

lemma not_false' : ¬ false := _

/-
For any proposition, P, to prove ¬P,
assume that P is true and show that
that leads to a contradiction (in the
form of a proof of false). This is 
called "proof by negation." Remember:
¬P means P → false.
-/