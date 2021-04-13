import ...inClassNotes.langs.bool_expr
import data.bool


/- 1. [20 points]

The proof that e1 && e2 is semantically equivalent to e2 && e1
in our little language of Boolean expressions *broke* when we
added state as an argument to the evaluation function (which we
needed when we added Boolean variables to our language). Your
job here is to repair/evolve the initial proof, just below, in
light of these changes in the software about which it proves 
that property. Hint: Be sure to add a state argument everywhere
one is needed. Here's the original proof. Just fix it here.
-/
example : ∀ (e1 e2 : bool_expr), 
  bool_eval (e1 ∧ e2) = bool_eval (e2 ∧ e1) 
  :=
begin
  assume e1 e2,
  simp [bool_eval],
  cases (bool_eval e1),
  cases (bool_eval e2),
  apply rfl,
  apply rfl,
  cases (bool_eval e2),
  repeat {apply rfl},
end

/- 2. [20 points]

An identity in Boolean algebra is that P → Q is equivalent 
to ¬P || Q. We want to know that our language and semantics
correctly implement Boolean algebra. One way to improve our
confidence is to prove that the algebra we've implemented
has the properties we expect and require of Boolean algebra.
Hint: The following proposition captures this expectation. 
Prove it.

A note to you: When trying to prove this proposition, I
got stuck. That was due to a subtle bug in my definition
of our Boolean expressions language. I used ¬ for not but
|| and && for and and or, thus mixing notations generally
used for logic (¬) and computation (&& and ||). It turns
out that the precedence levels don't work when you do 
this, as && binds more tighly than ¬, meaning that ¬ P
∧ Q is read as ¬ (P ∧ Q). Oops! Good thing I tried to
prove something about our language! I fixed the notation
and was then able to push my proof through. As you gain
experience using verification tools and methods, you'll
find that they really do find bugs in code!
-/

example : ∀ (e1 e2 : bool_expr) (st: bool_var → bool), 
  bool_eval (¬e1 ∨ e2) st = bool_eval (e1 => e2) st  := 
begin
  -- your answer
end


/- 3. [40 points]

As mentioned (but not explained) in class, we can formalize the 
semantics of a language not as a function from expressions (and
state) to values, but as a *relation* between expressions (and
state) and values. To this end, we need rules for proving that
an expression has a given value (in a given state). 

Here, then, is a partial specification of the semantics of our
Boolean expression language in the form of an inductive type 
family. Take a glance, then continue with the explanation below
and refer back to this definition as needed.
-/

open bool_expr

/-
We start by defining a predicate, bool_sem, with three arguments:
a state, and expression, and a Boolean value. Applying bool_sem to
such arguments (let's call them st, e, and b), yields a proposition,
(bool_sem st e b). This proposition asserts that in state st, the
expression, e (in our language), has as its semantic meaning the 
Boolean value, b. 
-/

inductive bool_sem : (bool_var → bool) → bool_expr → bool → Prop

/-
Such a proposition might or might not be true, of course. We now
define the rules for reasoning about when one is true. We give a
semantic rule for each form of expression in our language.

The first rule, lit_sem, says that if we're given a Boolean value,
b, an expression in our language, e, and a state, st, then the 
three-tuple, (st, [b], b), is "in" our semantic relation. Be sure
you see why: For our language to mean what we want it to mean, a
literal expression, [b], better mean b, no matter the state, st. 
-/
| lit_sem (b : bool) (e : bool_expr) (st : bool_var → bool) : bool_sem st [b] b

/-
The next rule says that if we're given a variable v, an expression
e, and a state, st, then the meaning of a variable expression is (st 
v). This proof constructor is axiomatic: We are stating that this is
what we want expressions in our language to mean.
-/
| var_sem (v : bool_var) (e : bool_expr) (st : bool_var → bool) : bool_sem st [v] (st v)

/-
Finally, if e1 and e2 are expressions, st is a state, b1 and b2 are
bools, and the meaning of e1 in st is b1, and the meaning of e2 in st
is b2, then the meaning of (e1 ∧ e2) in st is the Boolean, b1 && b2.
-/
| and_sem : ∀ (e1 e2 : bool_expr) (st : bool_var → bool) (b1 b2 : bool), 
      bool_sem st e1 b1  → bool_sem st e2 b2 → bool_sem st (e1 ∧ e2) (b1 && b2)

/- 3A:

Extend this declarative/logical specification of the semantics of
our language with rules specifying the meaning of expressions formed
by ∨, ¬, and =>, respectively, and include comments like the ones just
above under each new constructor to explain what it specifies. Just
add your additional constructors to the preceding code in this file.
-/

/- 3B. Challenging. Extra credit for undergraduates. Required for
graduate students. Here you are asked to prove that for any two
expressions, e1 and e2, any state, st, and any Boolean value, v,
that the meaning of the expression, (e1 ∧ e2), in the state st, 
in our language, is always the same as that of (e2 ∧ e1) in st.
(The order of the sub-expressions is reversed.)

We give you the statement of the conjecture to be proved, along 
with a few hints:

Hint #1: You might have to rewrite an expression (band b1 b2),
i.e., (b1 && b2), as (b2 && b1) to make the proof go through.
Lean's libraries provide a theorem called bool.band_comm that
enables this rewriting. To do the rewriting, use the rw tactic
like this: rw bool.band_comm.

Hint #2: Don't forget: the "cases" tactic not only gives you
one case for each constructor of a value in your context but
*also* destructures it, assigning names to each of the values
that must have gone into forming that object. If you get stuck
at a point where you've got a proof object in your context
that seems like it contains information that would be useful
to you, destructure it using cases. 

Hint #3: You will have to *apply* the rule for reasoning about
conjunction expressions, bool_sem.and_sem, to the right argument
values to construct a required proof term (to satisfy a subgoal). 
You will have to begive the expression and state arguments, but 
Lean  should be able to infer the Boolean value arguments.

Hint #4: You win when you reduce a goal to one for which you
already have a proof. Then you can use the exact, assumption,
or trivial tactic to use that proof. 

Hint #5: Don't forget that to prove a bi-implication, P ↔ Q,
you will have to give proofs in both directions. Applying 
iff.intro, or just using the split tactic, will give you
the two subgoals to prove. I always celebrate when I get
half-way through, having solved one goal, only to quickly 
sober up when I realize I have another whole goal to prove.

Happy news: The reverse proof is symmetrical with the one
in the forward direction, so once you have the first half
done, you're close to being finished. It doesn't always
work this way, but here we're lucky. Also, we've given
you both the proposition to be proved and the first few
"moves."
-/
#check bool.band_comm

example : ∀ (e1 e2 : bool_expr) (st : bool_var → bool) (b : bool), 
  bool_sem st (e1 ∧ e2) b ↔ bool_sem st (e2 ∧ e1) b :=
begin
  intros,
  split,

  -- forward direction
  assume h,


  -- reverse direction

end

/- 4. [20 points]

Give a declarative semantics for our language or arithmetic
expressions equivalent to that of our operational semantics. Graduate
students, extra credit for undergraduates: prove that, given our 
semantics, the meaning of e1 + e2 is the same as that of e2 + e1, 
in any state. 
-/

-- HERE