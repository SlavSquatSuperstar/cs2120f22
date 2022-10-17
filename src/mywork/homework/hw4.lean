/-
Eric Weng (qgt7zm)
CS 2120 Homework 4
Sun 10/16/22
Proofs in Lean
-/

/- #1A [10 points]

Write p_qr formal proposition stating that 
logical and (∧) is associative. That is, 
for arbitrary propositions, P, Q, and R,
P ∧ (Q ∧ R) is true *iff* (P ∧ Q) ∧ R is, 
too. Replace the placeholder (_) with your
answer.
-/

def and_associative : Prop := 
  -- Given
  ∀(P Q R : Prop),
  -- Prove  
  P ∧ (Q ∧ R) ↔ (P ∧ Q) ∧ R


/- #1B [10 points]

Give an English language proof. Identify
the inference rules of predicate logic
that you use in your reasoning.

Answer: 

Our goal is to prove P ∧ (Q ∧ R) is true iff (P ∧ Q) ∧ R is true, for any propositions P, Q, and R.
To prove a bi-implication for two propositions, we can use iff intro on both single-direction implications.

First, prove P ∧ (Q ∧ R) implies (P ∧ Q) ∧ R.
1. Assuming P ∧ (Q ∧ R) is true, use and elimination a few times to prove that
P is true, Q is true, and R is true (all separate propositions are true).
2. Use and introduction a few times to build (P ∧ Q) ∧ R from all three propositions.

Second, prove (P ∧ Q) ∧ R implies P ∧ (Q ∧ R).
1. Assuming (P ∧ Q) ∧ R is true, use and elimination a few times to prove that
P is true, Q is true, and R is true (all separate propositions are true).
2. Use and introduction a few times to build P ∧ (Q ∧ R) from all three propositions.

Finally, we can apply iff introduction to both implications to conclude P ∧ (Q ∧ R) ↔ (P ∧ Q) ∧ R.
-/

/- #1C [5 points]

Give p_qr formal proof of the proposition.
Hint: unfold and_associative to start.
-/

-- ∀(P Q R : Prop), P ∧ (Q ∧ R) ↔ (P ∧ Q) ∧ R
theorem and_associative_true : and_associative :=
begin
  unfold and_associative,
  assume P Q R, -- for-all intro

  -- Prove iff intro
  apply iff.intro,

  -- Prove forward implication
  assume p_qr : P ∧ (Q ∧ R),          -- arrow intro

    -- Prove (P ∧ Q) ∧ R
    cases p_qr with p qr,             -- P and Q ∧ R
    cases qr with q r,                -- Q and R
    let pq : P ∧ Q := and.intro p q,  -- P ∧ Q
    exact and.intro pq r,

  -- Prove reverse implication
  assume pq_r : (P ∧ Q) ∧ R, -- arrow intro

    -- Prove P ∧ (Q ∧ R)
    cases pq_r with pq r,             -- P ∧ Q and R
    cases pq with p q,                -- P and Q
    let qr : Q ∧ R := and.intro q r,  -- Q ∧ R
    exact and.intro p qr,

end

/- #2A [10 points]

Write the proposition that ∨ is associative.,
analogous to the proposition about ∧ in #1.
-/

def or_associative : Prop := 
  -- Given
  ∀(P Q R : Prop),
  -- Prove
  -- P ∨ (Q ∨ R) → S ↔ (P ∨ Q) ∨ R → S
  P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R


/- #2B [10 points]

Write an English language proof of it, citing
the specific inference rules you use in your
reasoning.

Answer: 

Our goal is to prove P ∨ (Q ∨ R) is true iff (P ∨ Q) ∨ R is true, for any propositions P, Q, and R.
To prove a bi-implication for two propositions, we can use iff intro on both single-direction implications.

First, prove P ∨ (Q ∨ R) implies (P ∨ Q) ∨ R.
1. Assuming P ∨ (Q ∨ R) is true, use or elimination a few times to prove
P is true, Q is true, or R is true (three separate cases where one proposition is true).
2. Use or introduction a few times to build P ∨ (Q ∨ R) from each case.

Second, prove (P ∨ Q) ∨ R implies P ∨ (Q ∨ R).
1. Assuming P ∨ (Q ∨ R) is  true, use or elimination a few times to prove
P is true, Q is true, or R is true (three separate cases where one proposition is true).
2. Use or introduction a few times to build P ∨ (Q ∨ R) from each case.

Finally, we can apply iff introduction to both implications to conclude P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R.
-/


/- #2C [5 points]

Complete the following formal proof.
∀(P Q R : Prop), P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R
-/

theorem or_associative_true : or_associative :=
begin
unfold or_associative,
assume P Q R,

split, --same as apply iff.intro,

-- First implication
assume p_qr : P ∨ (Q ∨ R),
  -- get P ∨ Q ∨ R to be true
  cases p_qr with p qr,
    -- if P
    let pq : P ∨ Q := or.inl p,    -- P ∨ Q
    exact or.inl pq,               -- (P ∨ Q) ∨ R

    cases qr with q r,
      -- if Q
      let pq : P ∨ Q := or.inr q,  -- P ∨ Q
      exact or.inl pq,             -- (P ∨ Q) ∨ R

      -- if R
      exact or.inr r,              -- (P ∨ Q) ∨ R

-- Second implication
assume pq_r : (P ∨ Q) ∨ R,
  -- get P ∨ Q ∨ R to be true
  cases pq_r with pq r,
    cases pq with p q,
      -- if P
      exact or.inl p,              -- P ∨ (Q ∨ R)

      -- if Q
      let qr : Q ∨ R := or.inl q,  -- Q ∨ R
      exact or.inr qr,

    -- if R
    let qr : Q ∨ R := or.inr r,  -- Q ∨ R
    exact or.inr qr,

end


/- #3A [10 points]
Write p_qr formal statement of the proposition.
-/

def arrow_transitive : Prop :=
  -- Given
  ∀(X Y Z : Prop),
  (X → Y) →
  (Y → Z) →
  -- Prove
  (X → Z)


/- #3B [10 points]

Write an English language proof of the proposition
that for any propositions, X, Y, and X, it's the
case that (X → Y) → (Y → Z) → (X → Z). In other
words, implication is "transitive." Hint: Recall
that if you have p_qr proof of, say, X → Y, and you 
have p_qr proof of X, you can derive p_qr proof of Y by
arrow elimination. Think of it as applying p_qr proof
of an implication to p_qr proof of its premise to get
yourself p_qr proof of its conclusion.

For any propositions X, Y, and Z
If we know that X implies Y, and Y implies Z, and we want to prove X implies Z,
If we assume X is true, we can deduce that Y is true,
And then since Y is true we can deduce that Z is true.
-/


/- #3C [5 points]. 
Write p_qr formal proof of it.
-/
theorem arrow_transitive_true : arrow_transitive :=
begin
unfold arrow_transitive,
assume X Y Z,

assume xy : X → Y,
assume yz : Y → Z,
assume x : X,

apply yz, -- need p_qr proof of y for z
apply xy, -- need p_qr proof of x for y
exact x,  -- consume p_qr proof of x
end


/- #4
Suppose that if it's raining then the streets
are wet. This problem requires you to prove that
if the streets are not wet then it's not raining.
-/

/- #4A [10 points]

Start by writing the proposition in predicate
logic by completing the following answer.
-/

def contrapositive : Prop :=
  ∀ (Raining Wet : Prop), 
    -- (Raining → Wet) → (¬Raining → ¬Wet) -- doesn't match English story
    -- The statement in its original form is a fallacy (denying the antecedent)
    (Raining → Wet) → (¬Wet → ¬Raining)


/- #4B [10 points]. 

Write p_qr formal logic proof of the proposition.
-/

theorem contrapositive_valid : contrapositive :=
begin
  unfold contrapositive,
  assume Raining Wet,       -- for-all intro
  assume rw: Raining → Wet, -- arrow intro

  -- prove ¬W → ¬R
  assume nw: ¬Wet,          -- arrow intro again

    -- prove ¬R (same as R → false) through negation
    assume r: Raining,      -- assume the opposite
    let w : Wet := (rw r),  -- apply r : R to R → W to prove W
    let f := (nw w),        -- apply w : W to ¬W  to prove ¬W
    exact f                 -- this is an impossibility; we assumed W
end

/- #4C [5 points]. 

Give an English language proof of it.

Assuming it is Raining and Wet are any propositions through for-all intro
-/


/- #5. Extra credit.

Complete the following formal proof of the 
proposition that if for any proposition P, 
P ∨ ¬P is true, then for any propositions, 
X and Y, if it's not the case that X or Y
is true then it is the case that ¬X and ¬Y 
is true. 
-/

-- ¬(X ∨ Y) → (¬X ∧ ¬Y)
theorem demorgan1 : 
  (∀ (P : Prop), P ∨ ¬ P) → 
    ∀ (X Y : Prop), 
      ¬(X ∨ Y) → (¬X ∧ ¬Y) :=
begin
  assume em,                  -- excluded middle rule
  assume X Y,
  assume n_xy,                -- arrow intro premise ¬(X ∨ Y)

  -- prove ¬X ∧ ¬Y
  cases (em X) with x nx,     -- apply excluded middle to X
    -- X is true (proof by contradiction)
    let xy := or.inl x,       -- X ∨ Y
    let f := n_xy xy,         -- X ∨ Y contradicts with ¬(X ∨ Y)
    exact false.elim f,       -- conclude true through contradiction

    -- ¬X is true
    cases (em Y) with y ny,   -- apply excluded middle to Y
      -- Y is true
      let xy := or.inr y,     -- X ∨ Y
      let f := n_xy xy,       -- X ∨ Y contradicts with ¬(X ∨ Y)
      exact false.elim f,     -- conclude true through contradiction

      -- ¬Y is true
      exact and.intro nx ny,  -- combine ¬X and ¬Y to conclude ¬X ∧ ¬Y

end

/-
A comment on or.intro_left and or.intro_right.
In Lean each of these takes two arguments: p_qr
proof of the disjunct -- the proposition on 
one side of the ∨ -- that is to be proven true, 
*and* it takes as an argument the proposition 
that is not being proven true. In applications 
of these rules the proposition argument (not 
being proven) comes first, while the proof 
argument comes second.

The reason is that Lean needs to know what 
overall proposition is being proved. From the
proof argument it can infer the proposition 
being proved, but it needs the other proposition
as well to know the full (X ∨ Y) disjunction to
be proved. 

Here's an example:
-/

example : 0 = 0 ∨ 0 = 1 :=
begin
apply or.intro_left (0 = 1) rfl
/-
The "rfl" serves as p_qr proof of 0=0.
But in addition, as the first argument
to or.intro, we need to provide the
*proposition* that is not being proved.
Here's that's (0 = 1). In contexts
where Lean can infer both disuncts,
you can use the simpler or.inl or 
or.inr, each of which just takes one
argument: p_qr proof of the left or of 
the right side, respectively.
-/
end
