variables X Y Z : Prop

/- *** And (∧) Rules *** -/

def and_introduction  : Prop  := ∀ (X Y), X → Y → (X ∧ Y)
def and_elim_left     : Prop  := ∀ (X Y), X ∧ Y → X  
def and_elim_right    : Prop  := ∀ (X Y), X ∧ Y → Y  

/- *** Or (∨) Rules *** -/

def or_intro_left : Prop    := X → X ∨ Y
def or_intro_right : Prop   := Y → X ∨ Y
def or_elim : Prop          := (X ∨ Y) → (X → Z) → (Y → Z) → Z 
-- provable by 2 cases

/- *** Iff (↔) Rules *** -/

-- Derived from and rules
def iff_intro               := (X → Y) → (Y → X) → X ↔ Y
def iff_elim_left           := X ↔ Y → (X → Y)
def iff_elim_right          := X ↔ Y → (Y → X)

/- *** For-all (∀) and Implies (→) Rules *** -/

def implies_forall_equiv    := (∀ (x : X), Y) ↔ (X → Y)
def implies_elim            := (X → Y)        → X   → Y
def forall_elim             := (∀ (x : X), Y) → X   → Y

-- To prove for all x, y is true, assume an arbitrary x and prove x → y
-- To prove x → y, assume x is true, then in that context show y is true

/- *** True and False Rules *** -/
theorem true_is_true : true := true.intro
/- theorem proof_of_false : false := _ -/
-- no cases to consider

def false_elim       := ¬X → Y

/- Implication Outcomes -/

def p1 : Prop := false → false            -- provable with false elim
def p2 : Prop := false → true             -- provable with false elim
def p3 : Prop := true → true              -- provable with true intro or case analysis
def p4 : Prop := true → false             -- not provable because no proof of false
def p5 : Prop := false → 2 = 3            -- provable with false elimination
def p6 : Prop := false → 0 = 0            -- provable with reflexive property
def p7 : Prop := ∀ (P : Prop), true → P   -- not possible because proof of true is useless
def p8 : Prop := ∀ (P : Prop), false → P  -- provable with false elim

-- True introduction is not very useful
-- False is unprovable because is not true
-- False elimination: if false is true, then anything follows
-- If we derive a contradiction (inconsistent assumption), then anything is true

/- *** Not (¬) Rules *** -/

def neg (X : Prop) := X → false
-- ¬P == P → false
-- If not P is true, then P has no proofs
-- There are no proofs of false, so we have no proofs of P
-- If there was a proof of P, then false would have a proof (contradiction)
def neg_elim          := ¬¬X → X