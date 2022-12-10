
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

/- *** Propositional Laws of Reasoning ***
1. Identity: ∀ x, x = x (All objects are equal to themselves)
2. Non-Contradiction: ∀ x, ¬(x ∧ ¬x) (Propositions must either be true or not true)
3. Excluded Middle: ∀ x, x ∨ ¬x (Propositions are either true or false)
-/

/- *** Predicate vs Propositional Logic ***
Propositional Logic:
- Has no data types; e verything is a proposition
- Cannot quantify over anything (every, some, no)
- Cannot parameterize propositions
Predicate Logic:
- Cannot use truth tables to check validity
- Requires deductive reasoning for proofs and truth judgments
- Only objects as types
- Can only quantify over sets of objects
Constructive Logic:
- Cannot use excluded middle
-/


variables X Y Z : Prop -- Shorthand for declaring variables
-- We can quantify over propositions in HOCL (adds implict ∀)

/- Introduction vs Elimination
Introduction rules produce a proof
Elimination rules consume a proof
-/

/- *** Laws of Reasoning *** -/
def excluded_middle (P: Prop) : Prop := P ∨ ¬P
-- proof that p is true or false even if we don't have a proof 
-- only 2 cases to consider
-- works in both CL and PL

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
-- To prove for all X, Y is true, 1. Assume an arbitrary X and 2. prove X → Y
-- To prove X → Y, assume X is true, then in that context show Y is true
-- In HOCL, X → Y is a shorthand for ∀ (x: X) → Y

-- Arrow Elimination
-- If f: S → N and we want to prove N, we need a proof of S, s: S
-- In other words, (f s): N applies the proof f to s to prove N
-- Just function application

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

def not_intro (X : Prop) := X → false

/- Two proofs:

A) Proof by Negation (not introduction)
(P → false) → ¬P
To prove ¬P (P is false):
- 1. Assume P is true,
- 2. Show it leads to an impossibility
- 3. Conclude ¬P

-- If not P is true, then P has no proofs
-- There are no proofs of false, so we have no proofs of P
-- If there was a proof of P, then false would have a proof (contradiction)

B) Proof by Contradiction
(¬P → false) →  ¬(¬P) → P
To prove P (P is true):
- 1. Assume ¬P (P is false),
- 2. Show it leads to an impossibility, usually by applying P to a proof requiring ¬P
- 3. Conclude ¬(¬P) and use negation elimination/excluded middle to equate it to P
-/

def not_elim := ¬¬X → X
-- Not possible in constructive logic
-- Works if excluded middle is true

/- *** Exists (∃) Rules *** -/

def exists_intro := ∀ (P : X → Prop) (w : X), P w → (∃ (x : X), P x) 
-- To prove there exists an X with property P,
-- Supply a witness, w : X, and a proof of (P w)

def exists_elim := ∀ (P : X → Prop), (∃ (x : X), P x) → (∀ (x : X), P x → Y) → Y
-- If there exists an X with property P,
-- We can deduce a proof x : X and of (P x)
-- The exact identity of the witness is unknown, only its existence
-- And if (P x) proves Y, we can do so

/- *** Equals (=) Rules *** -/
/- Axioms of Equality

1. Reflexive property (introduction): given a value of any type, that value is equal to itself
  -- eq.refl takes 1 argument
  -- rfl takes 0 arguments
2. Substitutive property (eliminateion): if two objects are equivalent, then any property of the first
is present on the second
3. Symmetric: if a = b, then b = a
3. Transitive: if a = b and b = c, then a = c
-/