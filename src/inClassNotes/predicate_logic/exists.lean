/-
Exists introduction. To prove ∃ (p : P), Q
-/

/-
A proof of ∃ (p : P), Q is a *dependent* pair,
⟨ p, q ⟩, where (p : P) is a "witness" to the
existential proposition, and q is a proof of 
Q. 

Very often, Q will be *about* p, e.g., that
p is an "odd prime", or a "nice person". Q 
will be the result of aplying a predicate Q'
to P. Q is short for Q' p, with Q' : Person 
→ Prop being a property of a person, such as
the property of being nice. 

∃ (p : Person), Q' p thus asserts that there 
is *some* person with property Q'. So a proof
of this proposition will be a dependent pair,
⟨ (p : P), (q : Q' p) ⟩, with Q' a predicate
on values, p, of type P.
-/

example : ∃ (n : nat), n = 0 :=
⟨ 0, rfl ⟩ 

/-
There exists a natural number that is the square
of another natural number. 
-/
example : ∃ (n : nat), ∃ (m : nat), n = m*m :=
⟨4, ⟨2, rfl⟩ ⟩ 


/-
If everyone likes Mary then someone likes Mary.
-/
axiom Person : Type
axiom Mary : Person
axiom Likes : Person → Person → Prop


example : 
(∀ (p : Person), Likes p Mary) → 
(∃ (q : Person), Likes q Mary) :=
begin
  assume h,
  refine ⟨Mary, _⟩,
  apply h Mary,
end 