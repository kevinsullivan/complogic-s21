import .arith_expr
import .bool_expr


/- 
Syntax of our little language (OLL).
OLL supports mutable variables and
values of types arithmetic (bool) and 
arithmetic (nat). It has an assignment
command for each of these two types.
It also supports sequential composition
of smaller programs into larger ones.
-/
inductive cmd : Type
| skip 
| a_assn (v : var nat) (e : arith_expr) 
| b_assn (v : var bool) (e : bool_expr) 
| seq (c1 c2 : cmd) : cmd
| ifelse (b : bool_expr) (c1 c2 : cmd)

-- | cond (b : bool_expr) (c1 c2 : cmd) : cmd
-- | while (b : bool_expr) (c : cmd) : cmd

open cmd

notation v = e := b_assn v e 
notation v = a := a_assn v a 
notation c1 ; c2  := seq c1 c2 
notation `cond ` b ` then ` c1 ` else ` c2 := ifelse b c1 c2

def c_eval : cmd → env → env
| skip st := st
| (b_assn v e) st  := override_bool st v e
| (a_assn v e) st  := override_nat st v e
| (c1 ; c2) st  := c_eval c2 (c_eval c1 st) 

-- new
| (cond b then c1 else c2) st := 
    if (bool_eval b st) 
      then c_eval c1 st
      else c_eval c2 st

inductive c_sem : cmd → env → env → Prop
| c_sem_skip : ∀ (st : env), 
    c_sem skip st st

| c_sem_arith_assn :
  ∀ (pre post : env) (v : var nat) (e : arith_expr),
    (override_nat pre v e = post) → 
    c_sem (a_assn v e) pre post

| c_sem_bool_assn :
  ∀ (pre post : env) (v : var bool) (e : bool_expr),
    (override_bool pre v e = post) → 
    c_sem (b_assn v e) pre post

| c_sem_seq :
  ∀ (pre is post : env) (c1 c2 : cmd),
  c_sem c1 pre is → 
  c_sem c2 is post →
  c_sem (c1 ; c2) pre post

  -- New

  | c_sem_if_false : 
    ∀ (pre is post : env) (b : bool_expr) (c1 c2 : cmd),
    bool_eval b pre = ff → 
    c_sem c2 pre post → 
    c_sem (ifelse b c1 c2) pre post

  | c_sem_if_true : 
    ∀ (pre is post : env) (b : bool_expr) (c1 c2 : cmd),
    bool_eval b pre = ff → 
    c_sem c1 pre post → 
    c_sem (ifelse b c1 c2) pre post