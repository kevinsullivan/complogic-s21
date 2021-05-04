import ...inClassNotes.langs.arith_expr

variables (P Q R : Prop)

/-
Excluded middle [25 points]
-/

-- A. 5 points

example : (¬P ∨ ¬Q) → ¬(P ∧ Q) :=
begin
assume h,
cases h,
assume k,
exact h k.left,
assume k,
exact h k.right,
end


-- B. 15 points

example : ¬(P ∧ Q) → (¬P ∨ ¬Q) :=
begin
assume h,
cases (classical.em P),
cases (classical.em Q),
exact false.elim (h (and.intro h_1 h_2)),
exact or.inr h_2,
exact or.inl h_1,
end


-- C. 5 Points. What do these examples teach 
-- us about DeMorgan's Laws in constructive logic?

/-
-/

/-
Recursive definitions (practice) [20 points]
-/


/- 15 points
A. Write a function, le : nat → nat → bool,
that returns true if the first argument is
*less than or equal to* the second, and false
otherwise. Hints: case analysis, recursion.
-/

def leq : nat → nat → bool
| 0 n := tt
| (n'+1) 0 := ff
| (n'+1)(m'+1) := leq n' m'


/- 10 points
B. Write a function, eqn : nat → nat → bool,
that returns true if the first argument is
*equal to* the second, and false otherwise.
Hints: case analysis, recursion.
-/

def eql : nat → nat → bool
| 0 0 := tt
| _ 0 := ff
| 0 _ := ff
| (n'+1)(m'+1) := eql n' m'


/-
Better Boolean expressions [25 points]

Consolidate our definitions of the syntax and
semantics of Boolean and arithmetic expressions
into a system. Leave each algebra implemented
in its own file. Now define two new forms of
Boolean expression, as follows:

(1) if N and M are arithmetic variable
expressions, tben leq_expr N M is a Boolean
expression. It should evaluate to Boolean
true (tt) if and ony if N evaluates to a
number that is less than or equal to M,
using your leq function from the previous
problem.

(2) if N and M are arithmetic variable
expressions, then eql_expr N M is also
a Boolean expression: one that evaluates
to tt if and only if N evaluates to a 
natural number (nat) that is equal to 
the number to which M evaluates, using
your eql function.

Submit your work as a pair of files,
with the bool file importing from the
arithmetic file to obtain support for
arithmetic expressions. Follow naming
conventions established in the files
we developed in class. Submit the two
files in addition to your completed
version of this file.
-/



/-
Mutable state and assignment [25 points]

In this problem, we will contine to represent 
a state, as we have in our previous work, as 
a function from variables (objects of a type,
var) to values (here of type nat). 
-/

structure Var : Type := (index : nat)
def State := Var → nat
def eqVar (v1 v2 : Var) : bool := v1.index = v2.index

/-
One of the profound differences between
imperative and functional programming is 
that in the former--in languages such as
Python and C--one assumes and is given a
*mutable* global state. That is not the
case in functional programming. While we
can bind variable names to values once, we
cannot update the values bound to variables
as computations progress. 

When programming in an imperative language,
by contrast, one has operations for free to
obtain the value associated with (to read)
a variable, and to override the value that
is associated with a variable (to write to
it). We call the write operation assignment.

To confuse humans who already understand
arithmetic, the designers of languages such
as Basic, C, Java, and Python use = as a 
concrete notation to invoke the assignment
operation. (It's only indirectly related to
the concept of equality from basic math.)

Thus in such languages we might write code
like this:

X = 1

Ignoring the terrible choice of notation
for what you can think of as a procedure
invocation (assign X 1), what this really 
means is *update the state so that the 
value of the variable X is now bound to 1.

What's missing from our X = 1 diagram,
though, is a representation of the states!
Here's a better picture, one that clearly
illustrates the *effect* of an assignment
operation on a state in one scenario. 

{ (X, 0), (Y, 1), (Z, 2) }
X = 1
{ (X, 1), (Y, 1), (Z, 2) }

In this case, the state before the assignment 
was given by the function, 
  st = { (X, 0), (Y, 1), (Z, 2) }, while after
the assignment operation it was 
  st' = { (X, 1), (Y, 1), (Z, 2) }.
Notice that st' differs from st only for X, and
the new value associated with X is the one that
we "assigned" to it.

Now read this carefully. We can now represent
an assignment operation in Lean as a function:
one that takes a state, st, a variable, v, and
a value, k, and that returns a state, st', that
differs from st only to the extent that in st',
v is bound to k, whereas every other variable 
remains bound to the value it had in st.
-/

def assign (st : State) (v : Var) (k : nat) : State :=
λ v', if (v.index = v'.index) then k else st v'


/-
Examples
-/

def allz : State := λ v, 0

#reduce allz


def X := Var.mk 0
def Y := Var.mk 1
def Z := Var.mk 2

/-
-- start in initial state
X = 7;
Y = 8;
Z = 9;
-/
def st := 
  assign 
    (assign 
      (assign 
        allz 
        X 
        7
      ) 
      Y 
      8
    ) 
    Z 
    9

#eval st X
#eval st Y
#eval st Z

-- Exercise: assign 10 to X after all that, call new state st'

def st' : State := _

#eval st' X
#eval st' Y
#eval st' Z

inductive cmd : Type
| assn (v : Var) (a : aexp)
| seq (c1 c2 : cmd) 

open cmd

notation v = aexp := assn v aexp 
notation c1 ; c2 := seq c1 c2

def a1 : cmd := X = [7]
def a2 : cmd := Y = [8]
def a3 : cmd := Z = [9]
def a4 : cmd := X = [10]

-- Need a way to compose these commands!

def c := a1; a2; a3; a4



#reduce st 
/-
-- a function that takes an argument, v', of type Var, and that returns its value
λ (v' : Var),
  decidable.rec

    -- case 1: if v' ≠ Z the return result of applying the function before the override
    (λ (hnc : 2 = v'.index → false),
       decidable.rec

          -- case A: v' ≠ Y
         (λ (hnc : 1 = v'.index → false),
            decidable.rec 
              
              -- case a: v' ≠ X
              (λ (hnc : 0 = v'.index → false), 0) 

              -- case b: v' = X
              (λ (hc : 0 = v'.index), 7)

              -- v' =? X decidable
              (nat.decidable_eq 0 v'.index))

          -- case B: v' = Y
         (λ (hc : 1 = v'.index), 8)
         (nat.decidable_eq 1 v'.index))

    -- case 2: if v' = Z then return the overriding value 
    (λ (hc : 2 = v'.index), 9)
    (nat.decidable_eq 2 v'.index)
-/
#check @decidable_eq
#check @nat.decidable_eq

/-
 In English, this is the state obtained by
 starting with an all-zeros state and then
 overriding X with 1, then overriding Y with
 5 in that state, and then overriding the
 result of that with Z 4.
 -/
 /-
 How is that concept of state implemented 
 using decidable.rec, answers, functions,
 or values? [?]
 -/
/-
Here's decidable.rec.
-/
#check @decidable
/-
class inductive decidable (p : Prop)
| is_false (h : ¬p) : decidable
| is_true  (h : p) : decidable
-/
#check @decidable.rec
/-
-- For any proposition, p, and a function 
-- from either a proof of p or a proof of
-- not p to a type inhabiting Sort u_1,
Π {p : Prop} {C : decidable p → Sort u_1},

-- assume we have a function that takes a
-- proof, h, that p is false, and returns
-- C applied to the proof that p is false, 
    (Π (h : ¬p), C (is_false h)) → 
-- assume we have a function that takes a
-- proof, h, that p is true, and returns
-- C applied to the proof that p is true, 

    (Π (h : p), C (is_true h)) → 
-- then for any (n : decidable p), or in
-- other words for either an is_true proof
-- or an is_false proof, there is a value
-- of type C n
Π (n : decidable p), C n

-- In other words, if you've given a value
-- for the true case and one for the false
-- case then you've covered all the cases,
-- and for each case you have a function to
-- convert a proof for that case into a type.
[SEEMS_WRONG]
-/

