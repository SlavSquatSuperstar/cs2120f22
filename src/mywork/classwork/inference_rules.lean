/- *** Inference Rules ***
2. X, Y ⊢ X ∧ Y              -- and introduction
3. X ∧ Y ⊢ X                 -- and elimination left
4. X ∧ Y ⊢ Y                 -- and elimination right
5. ¬¬X ⊢ X                   -- negation elimination 
6. ¬(X ∧ ¬X)                 -- no contradiction
7. X ⊢ X ∨ Y                 -- or introduction left
8. Y ⊢ X ∨ Y                 -- or introduction right
10. X → Y, Y → X ⊢ X ↔ Y      -- iff introduction
11. X ↔ Y ⊢ X → Y            -- iff elimination left
12. X ↔ Y ⊢ Y → X            -- iff elimination right
13. X ∨ Y, X → Z, Y → Z ⊢ Z  -- or elimination
15. X → Y, X ⊢ Y             -- arrow elimination
16. X → Y, Y → Z ⊢ X → Z     -- transitivity of → 
18. X → Y ⊢ ¬Y → ¬X          -- contrapositive
19. ¬(X ∨ Y) ↔ ¬X ∧ ¬Y       -- DeMorgan #1 (¬ distributes over ∨)
20. ¬(X ∧ Y) ↔ ¬X ∨ ¬Y       -- Demorgan #2 (¬ distributes over ∧)
-/

/- *** Logical Fallacies ***
1. X ∨ Y, X ⊢ ¬Y             -- affirming the disjunct (invalid)
9. X → Y, ¬X ⊢ ¬ Y           -- denying the antecedent (invalid)
14. X → Y, Y ⊢ X             -- affirming the conclusion (invalid)
17. X → Y ⊢ Y → X            -- converse (invalid)
-/


variables X Y Z : Prop -- Shorthand for declaring variables
-- We can quantify over propositions in HOCL (adds implict ∀)

/- Introduction vs Elimination
Introduction rules produce a proof
Elimination rules consume a proof
-/

/- *** And (∧) Rules *** -/

def and_introduction  : Prop  := X → Y → (X ∧ Y)
def and_elim_left     : Prop  := X ∧ Y → X  
def and_elim_right    : Prop  := X ∧ Y → Y  

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

def implies_forall_equiv    := (∀ (x : X), Y) ↔ (X → Y) -- for-all introduction
def implies_elim            := (X → Y)        → X   → Y
def forall_elim             := (∀ (x : X), Y) → X   → Y

-- For-all Introduction
-- To prove for all X, Y is true, assume an arbitrary X and prove X → Y
-- To prove X → Y, assume X is true, then in that context show Y is true
-- In HOCL, X → Y is a shorthand for ∀ (x: X) → Y

-- X → Y → Z in HOCL is equivalent to X ∧ Y → Z in FOPL

/- *** True and False Rules *** -/

theorem true_intro : true := true.intro -- Not very useful
-- No true elimination rule

-- theorem false_intro : false := _
-- No false introduction: unprovable because false is not true (no cases to consider)

def false_elim       := ¬X → Y

-- False elimination: if false is true, then anything follows
-- If we derive a contradiction (inconsistent assumption), then anything is true

/- Implication Outcomes -/

def p1 : Prop := false → false            -- provable with false elim
def p2 : Prop := false → true             -- provable with false elim
def p3 : Prop := true → true              -- provable with true intro or case analysis
def p4 : Prop := true → false             -- not provable because no proof of false
def p5 : Prop := false → 2 = 3            -- provable with false elimination
def p6 : Prop := false → 0 = 0            -- provable with reflexive property
def p7 : Prop := ∀ (P : Prop), true → P   -- not possible because proof of true is useless
def p8 : Prop := ∀ (P : Prop), false → P  -- provable with false elim

/- *** Not (¬) Rules *** -/

def neg_intro (X : Prop) := X → false
-- Proof by negation (not introduction)
-- (P → false) ↔ ¬P
-- To prove something is false, assume it is true
-- and show it leads to an impossibility

-- If not P is true, then P has no proofs
-- There are no proofs of false, so we have no proofs of P
-- If there was a proof of P, then false would have a proof (contradiction)
def not_elim := ¬¬X → X