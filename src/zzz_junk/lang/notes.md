# JUNK IGNORE


/-
Try working backwards from example constructs
-/

/-
axioms 
(X Y Z : var nat)
(A B C : var bool)

eval : cmd → env → env 

e.g.,
#eval 
  eval
  (
    if (¬B && X < Y)
    then cmd1
    else cmd2
  )
  init_env 
=>
result depending on evaluation of
-- 
-/

/-
Think about categorical aspects of our structure.

* An infinite set of frame-indexed affine coordinate spaces (ACS) 

* A distinguished base affine space, std, to which every ACS maps.
* Transitive closure of the parent relation on frame-indexed ACSs
-/

/-
aside : nfts 4 sdev
-/