/-
How to inherit field values from parent objects.
-/


@[class] 
structure A (α : Type) := (n m : nat)
instance a : A nat := ⟨ 1, 4 ⟩              -- anonymous constructor
instance a' : A nat := { m := 4, n := 1 }  -- alternative notation for objects
#reduce a
#reduce a'

class B (α : Type) := (h : nat) (k : nat)
instance b : B nat := ⟨ 2, 3 ⟩ 
#reduce b

#check @B.mk

class C (α : Type) extends A α, B α := (c : nat)
instance c : C nat := { c := 3, ..a, ..b } 
#check @C nat
#check @c
#reduce c

class C' (α : Type) extends A α, B α := (c : nat)
instance c' : C' nat := ⟨ 3 ⟩ 
#check @C' nat
#check @c'
#reduce c'
#check @C'.mk

#check @C.mk


