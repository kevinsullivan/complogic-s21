/-
Alice is looking at Bob. Bob is looking at Charlie.
Alice is married. Charlie is not. 

Theorem to Prove: Some (∃) married person is looking at some unmarried person

(A) Yes
(B) No
(C) Cannot be determined
(D) It depends
-/

example : ∀ (P : Prop), P ∨ ¬P := 
begin
  assume P,
  apply or.inr _,
  intro p,
  _
end

/-
In constructive logic, ∀ (P : Prop), P ∨ ¬ P, 
is not provable.
-/

axioms
(Person : Type)
(Married : Person → Prop)
(LookingAt : Person → Person → Prop)
(alice bob charlie : Person)
(alab : LookingAt alice bob)
(blac : LookingAt bob charlie)
(am : Married alice)
(ncm : ¬Married charlie)

example : _ : _

/-
forall p1 p2, Married p1 and not married p2 and looking at p1 p2
-/

example : ∀ (p1 p2 : Person), 
    Married p1 → ¬ Married p2 → LookingAt p1 p2 := _

/- 
Every married person is looking at every unmarried person.
This is not quite the right formalization.
-/


/-
Some married person, p1, is looking at some unmarried person, p2.
This is the formalization that we want. Now the question is, can
we prove it?
-/
example : ∃ (p1 : Person), ∃ (p2 : Person), Married p1 ∧ ¬Married p2 ∧ LookingAt p1 p2 := 
begin
apply exists.intro alice,
apply exists.intro bob,
split,
apply am,
split,
end

-- STUCK!

example : ∃ (p1 : Person), ∃ (p2 : Person), Married p1 ∧ ¬Married p2 ∧ LookingAt p1 p2 := 
begin
apply exists.intro bob,
apply exists.intro charlie,
split,
end

-- STUCK

/-
In constructive logic, we don't know that it's true 
that Bob is married or Bob is not married, whereas
in classical reasoning that would always be true, 
even if we don't know which case holds.

In constructive logic, for any proposition, P, there
are three possibilities:

(1) We have a proof of P
(2) We have a proof of ¬P
(3) We don't have a proof either way! This is the "MIDDLE!"

In computer science and mathematics, there are plenty of
examples where we don't know which case holds.
  - polynomial time (P) = non-deterministic polynomial time (NP)? TSP, Boolean SAT
  - Collatz conjecture -- hailstone program terminates on all inputs
-/

/-
meta def HS (n : nat) :=
if (n = 1 ∨ n = 0) return 0
else (if n%2 = 0) (HS n/2)
else (if n%2 = 1) (HS n*3+1)

Does this function terminate for all inputs n?

5 -> 8 -> 4 -> 2 -> 1 .
7 -> 22 -> 11 -> 34 -> 17 -> 51 -> 154 -> 77 -> ...
-/


/-
One might believe that constructive logic is weaker
than classical logic in the sense that there are 
propositions that are provable in the latter but
not in the former. On the other hand, we can always
reason classically in constructive logic by simply
introducing the "law of the excluded middle" as an
axiom. What it says is that for any proposition, P,
whatsoever, P ∨ ¬P is true in the sense that we can
assume that we have a proof of it. The trick is then
to do case analysis on such a *proof object*.
-/
axiom em : ∀ (P : Prop), P ∨ ¬ P

example : ∃ (p1 : Person), ∃ (p2 : Person), Married p1 ∧ ¬Married p2 ∧ LookingAt p1 p2 :=
begin
  cases (/-proof of (bim or bnm)-/ em (Married bob)), --!!!
  -- Married bob
  apply exists.intro bob,
  apply exists.intro charlie,
  split,
  assumption,
  split,
  exact ncm,
  exact blac,
  apply exists.intro alice,
  apply exists.intro bob,
  split, 
  exact am,
  split,
  assumption,
  exact alab,
end

-- Yay

/-
The axiom of the excluded middle is defined in the Lean library.
You can always apply it, but in general you will want to think
about the tradeoffs that are involved. Among the losses are (1)
you will no longer have any *evidence* for which case is true,
(2) you will be unable to extract runnable code from a proof of
a disjunction, because such a proof is just made from thin air:
it contains no proof/evidence either way but only says that one
of them must be true. 
-/
#check classical.em


theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P h,
  /-
  (¬ P -> false)
  ((P → false) → false)
  P?
  -/
  have ponp := classical.em P,
  cases ponp,
  assumption,
  contradiction,
end

/-
DeMorgan's laws
¬ (P ∧ Q) ↔ (¬P ∨ ¬Q)
¬ (P ∨ Q) ↔ (¬P ∧ ¬Q)
-/

theorem dm1 : ∀ (P Q : Prop), ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := 
begin
  intros,
  split,
  -- forward
  assume h,
  -- have: P ∧ Q → false
  
end

theorem dm2 : ∀ (P Q : Prop), ¬ (P ∨ Q) ↔ (¬P ∧ ¬Q) := 
begin
end


