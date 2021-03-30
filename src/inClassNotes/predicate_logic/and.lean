/-
The connective, and, in predicate as in
propositional logic builds a proposition
that asserts that each of two propositions
is true. Given propositions P, Q, P ∧ Q 
is also a proposition, and we judge it to
be true iff we just P to be true and we
judge Q to be true. We judge P and Q to
be true iff we have evidence that they
are true, in the form of proofs. Our rule
for constructing evidence for P ∧ Q thus
demands evidence for P and evidence for
Q and yields evidence for P ∧ Q. 
-/

#check and

/-
structure and (a b : Prop) : Prop :=
intro :: (left : a) (right : b)
-/

-- A polymorphic product type (in Prop)!

axioms (P Q : Prop) (p : P) (q : Q)

example : P := p
example : Q := q
example : P ∧ Q := and.intro p q
def paq : P ∧ Q := ⟨ p, q ⟩ 

#check and.elim_left

/-
def and.elim_left {a b : Prop} (h : and a b) : a := h.1
def and.elim_right {a b : Prop} (h : and a b) : b := h.2
-/

#reduce and.elim_left paq
#reduce and.elim_right paq

example : 0 = 0 ∧ 1 = 0 :=
_

