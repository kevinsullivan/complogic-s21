import data.real.basic
import .lin2k


-- Let's work with rational number field
abbreviation K := ℚ  

-- Here are nice abbreviations for types
abbreviation scalr := K
abbreviation vectr := K × K

/-
1A. [10 points]

Declare v1, v2, and v3 to be of type
vectr with values (4,6), (-6,2), and
(3, -7), respectively.
-/

-- HERE

/-
1B. [10 points]

Now define v4, *using the vector 
space operators, + and •, to be 
the following "linear combination"
of vectors: twice v1 plus negative 
v2 plus v3. The negative of a vector
is just -1 (in the field K) times
the vector. Write -1 as (-1:K), as 
otherwise Lean will treat it as the 
integer -1. (Note that subtraction
of vectors, v2 - v1 is defined as
v2 + (-1:K) • v1.)
-/

-- HERE 

/-
Compute the correct answer by hand
here, showing your work, and check
that eval is producing the correct
answer. 

-- HERE

-/

/-
1C. [10 points]

On a piece of paper, draw a picture
of the preceding computation. Make a
Cartesian plane with x and y axes. 
Draw each vector, v1, v2, v3, as an
arrow from the origin to the point
designated by the coordinates of the
vector.

Scalar multiplication stretches or
shrinks a vector by a given factor.
Show each of the scaled vectors in 
your picture: 2 • v1 and (-1:K) • v2. 

Finally vector addition in graphical
terms works by putting the tail (non
arrow) end of one vector at the head
of the other then drawing the vector
from the tail of the first to the head
of the second. Draw the vectors that
illustrate the sum, 2 • v1 + (-1:K) • v2,
and then the sum of that with v3. You
should come out with the same answer
as before. Take a picture of your
drawing and upload it with your test.
-/

-- HERE

/-
2. [15 points]

Many sets can be viewed as fields. For 
example, the integers mod p, where p is
any prime, has the structure of a field
under the usual operations of addition
and multiplication mod p.

In case you forget about the integers 
mod n, it can be understood as the set
of natural numbers from 0 to n-1, where
addition and multiplication wrap around.

For example, the integers mod 5 is the
set {0, 1, 2, 3, 4}. Now 2 + 2 = 4 but
2 + 3 = 5 = 0. It's "clock arithmetic," 
as they say. Similarly 2 * 2 = 4 but 
2 * 3 = 6 = 5 + 1 = 0 + 1 = 1. 

To show informally that the integers 
mod 5 is a field you have to show that
every element of the set has an additive
inverse and that every element of the 
set but 0 has a multiplicative inverse.

Draw two tables below with the values
of the integers mod 5 in each of the 
left column. In the second column of
the first table, write in the additive
inverses of each element. In the second
table, write the multiplicative inverses.
-/

-- HERE

/-
4. [15 points]
Is the integers mod 4 a field? If so,
prove it informally by writing tables
giving the inverses. If not, show that
not every value in the integers mod 4
(except 0) has a multiplicative inverse,
identify a value that doesn't have an
inverse, and briefly explain why.
-/

-- HERE

/-
5. [20 points]
Write a function, sum_vectrs, that 
takes a list of our vectr objects as 
an argument and that reduces it to a 
single vector sum. To implement your
function use a version of foldr as we
developed it: one that takes an additive
monoid implicit instance as an argument, 
ensuring consistency of the operator we
are using to reduce the list (add) and 
the corresponding identity element. 
Copy and if needed modify the foldr
definition here. It should use Lean's 
monoid class, as we've done throughout
this exercise. You do not need to and
should not try to use our algebra.lean 
file. Test your function by creating a
list of vectrs, [v1, v2, v3, v4], from
above, compute the expected sum, and
show that your function returns the 
expected/correct result.
-/

-- HERE

/-
6. Required for graduate students,
optional extra credit for undergrads.

The set of integers mod p can be viewed
as a field with the usual addition and
multiplication operations mod p. These 
finite fields (with only a finite number 
of elements) play a crucial role in many 
areas of number theory (in mathematics), 
and in cryptography in computer science.


A. [20 points]

Instantiate the field typeclass for
fs (a prime). You 
may and should stub out the proofs 
all along the way using "sorry", but
before you do that, convince yourself
that you are *justified* in doing so.

Use a "fake" representation of the
integers mod 5 for this exercise: as
an enumerated type with five values. 
Call them zero, one, two, three, and
four. Then define two functions, 
z5add and z5mul, to add and multiply
values of this type. You can figure
out the addition and multiplication
tables and just write the functions
by cases to return the right result
in each case. Start with Lean's field
typeclass, see what you need to 
instantiate it, and work backwards, 
recursively applying the same method 
until your reach clases that you can
implement directly. Put your code for
this problem below this comment.

Replace the following "assumptions" 
with your actual definitions (commenting
out the axioms as you replace them). You
can right away right click on "field" and
"go to definition" to see what you need
to do. Solving this problem will require
some digging through Lean library code.
-/
axioms 
  (Z5 : Type) 
  (z5add : Z5 → Z5 → Z5)
  (z5mul : Z5 → Z5 → Z5)
  #check field Z5

-- HERE

/-
B. [15 points]

Given that you've now presumably
established that Z5 is a field,
let z5scalr be an abbreviation for
Z5, and z5vectr for Z5 ⨯ Z5. Then
use #eval to evaluate an expression
(that you make up) involving vector 
addition and scalar multiplication
using our new z5vectr objects, i.e., 
vectors over Z5. These vectors will
look like, e.g., (one, three). Work 
out the right answer by hand and
test your code to gain confidence 
that it's working correctly.
-/

inductive foo : Type
| bar

open foo 

def add_foo : foo → foo → foo
| foo.bar foo.bar := foo.bar

instance has_add_foo : has_add foo := ⟨ add_foo ⟩ 

#reduce (bar, bar) + (bar, bar)

-- HERE

/-
Take away: Instantiating a typeclass
for a given type can provide a whole
set of operations and notations that
you can use to "do algebra" with that
type. The underlying types themselves
can be very diverse. That is, we can
impose the same abstract interface on
sets of objects of different kinds, 
just as we previously imposed a group
API on the elements of the symmetry 
group, D4, of a square. Here we've now
seen that we can write vector space
algebra computations involving 2-D
vectors over both the rational and
the integers mod 5. It's in this 
sense that instantiating a typeclass
for a type provides a new "API" for
manipulating values of that type.

And while languages such as Haskell
do provide typeclasses, they don't
provide a language in which you can
declaratively express and give proofs
of the "rules" that structures have 
to follow to be valid instances. So,
welcome to Lean, a language in which
you can write mathematics and code,
with strong automated type checking
of both code and proofs. If it has to
be right (which is the case for much
crypto code), maybe write it like so!
-/

inductive three : Type
| O
| I
| II


def mult : three → three → three :=
begin
assume t1 t2, 
cases t1,
cases t2,
exact three.O,
exact three.O,
exact three.O,
cases t2,
exact three.O,
exact three.I,
exact three.II,
cases t2,
exact three.O,
exact three.O,
exact three.I,
end

open three 

#reduce mult II II

lemma one_mult : ∀ (t : three), mult I t = t := 
λ (t : three), 
  match t with
  | O   := eq.refl O
  | I   := rfl
  | II  := rfl
  end 