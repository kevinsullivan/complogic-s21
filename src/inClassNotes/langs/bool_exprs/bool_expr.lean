/-
true, 
false, 
true && false, 
(true && false) && true
-/

inductive bool_expr : Type
| lit_expr : bool → bool_expr 
| and_expr : bool_expr → bool_expr → bool_expr 

open bool_expr 

notation e1 && e2 := and_expr e1 e2
notation `[` b `]` := lit_expr b

def true_expr : bool_expr := [tt]
def false_expr : bool_expr := [ff]
def e3 := and_expr (lit_expr tt) [ff]
def e4 := and_expr e3 [tt]

notation e1 && e2 := and_expr e1 e2

def e3' := [tt] && [ff]
def e4' := e3 && [tt]

-- That's the syntax

-- Now for the semantics

def bool_eval : bool_expr → bool
| (lit_expr b) := b
| (and_expr e1 e2) := band (bool_eval e1) (bool_eval e2)

#eval bool_eval e4'