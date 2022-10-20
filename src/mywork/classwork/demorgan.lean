/-
Proving DeMorgan's Laws
Tue 10/18/22
-/

def dm1 : Prop := ∀ (A B : Prop), ¬(A ∧ B) ↔ ¬A ∨ ¬ B

example : dm1 :=
begin
  unfold dm1,
  assume A B, -- for-all intro
  apply iff.intro,

  -- first implication
  assume n_ab : ¬(A ∧ B), -- arrow intro
    -- negation -> use EM on A
    cases (classical.em A) with a na,
      
      -- A is true, use EM on B
      cases (classical.em B) with b nb,
        
        -- A ∧ B, contradicts premise
        let ab : A ∧ B := and.intro a b,
        -- let f : false := (n_ab ab),
        -- exact false.elim f,
        
        contradiction, -- this is shorthand

        -- ¬B
        exact or.inr nb,

      -- ¬A, B is anything
      exact or.inl na,

  -- second implication
  assume na_nb: ¬A ∨ ¬ B, -- arrow intro

  -- prove ¬(A ∧ B) by negation
  assume ab : A ∧ B,
  cases na_nb with na nb, -- disjunction -> case analysis
    -- ¬A
    -- let a : A := and.elim_left ab,
    -- let f : false := (na a),
    -- exact false.elim f,

    -- ¬B
    -- let b : B := and.elim_right ab,
    -- let f : false := (nb b),
    -- exact false.elim f,

    -- this is shorthand
    apply (na (and.elim_left ab)),
    apply (nb (and.elim_right ab)),

end

def dm2 : Prop := ∀ (A B : Prop), ¬(A ∨ B) ↔ ¬A ∧ ¬ B

example : dm2 :=
begin
  unfold dm2,
  assume A B, -- for-all intro
  apply iff.intro,

  -- first implication
  assume n_ab : ¬(A ∨ B),

    cases (classical.em A) with a na,
      -- A is true, B is anything
      let ax := or.inl a,
      contradiction,
      
      -- ¬A
      cases (classical.em B) with b nb,
        -- B is true
        let xb := or.intro_right A b,
        contradiction,

        -- ¬A ∧ ¬B
        exact and.intro na nb,

  -- second implication
  assume na_nb : ¬A ∧ ¬B,
  let na : ¬A := and.elim_left na_nb,
  let nb : ¬B := and.elim_right na_nb,

  assume ab : A ∨ B, -- proof by negation
  cases ab with a b,
  exact (na a),
  exact (nb b),
end