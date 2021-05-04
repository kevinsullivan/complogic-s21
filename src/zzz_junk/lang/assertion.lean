import .imp

-- An assertion is a predicate on system state
def Assertion := env → Prop

-- What it means for program c to satisfy pre/post spec
def satisfies (c : cmd) (pre post : Assertion) :=
  ∀ (st st' : env),
  pre st → 
  c_sem c st st' → 
  post st'

-- Hoare triple notation
notation pre {c} post := satisfies c pre post -- Hoare triple
