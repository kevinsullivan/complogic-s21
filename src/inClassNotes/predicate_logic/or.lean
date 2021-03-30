/-
If P and Q are propositions, then so in P ∨ Q.
We want to judge P ∨ Q to be true if at least
one of them is true. In other words, to judge
P ∧ Q to be true, we need either to be able to
judge P to be true or Q to be true (and if both
are true, that's fine, too).
-/

#check or

/-
inductive or (a b : Prop) : Prop
| inl (h : a) : or
| inr (h : b) : or
-/

/-
It's a polymorphic either type (in Prop)!
-/


axioms (P Q : Prop) (p : P)

lemma porq' : P ∨ Q := _

lemma porq'' : P ∨ Q := 
begin
end

axiom (q : Q)

lemma porq''' : P ∨ Q := _

/-
def or.intro_left {a : Prop} (b : Prop) (ha : a) : or a b :=
or.inl ha

def or.intro_right (a : Prop) {b : Prop} (hb : b) : or a b :=
or.inr hb
-/


/-
Suppose it's raining or the sprinkler is running.
Futhermore, suppose that if it's raining the grass
is wet, and if the sprinkler is running then the
grass is wet? What can you conclude? 
-/

/-
You *used* the fact that at least one of the cases
held, combined with the fact that in *either* case,
the grass is wet, to deduce that the grass is wet.
-/

axioms (R : Prop) (porq : P ∨ Q) (pr : P → R) (qr : Q → R)

theorem RisTrue : R := _


