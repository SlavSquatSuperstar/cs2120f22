/-
Existence Inference Rules in Lean
Thur 10/27/22
-/

def isEven : ℕ → Prop :=
begin
assume n,
exact (n%2 = 0)
end

example : ∃ (n : ℕ), isEven n :=
  exists.intro 8 rfl
  -- prove a witness satisfies the proposition

-- consume 8 and proof 8 is even to get exists statement
-- forgets the witness
-- example : (∃ (n : ℕ), isEven n) → isEven(n + 2) :=
-- begin
-- assume h
-- end

-- If there's someone that everyone loves, then everyone loves someone.
example
  (Person : Type)
  (Loves : Person → Person → Prop)
  :

  (∃ (P : Person), ∀ (Q : Person), Loves Q P) →
  (∀ (P : Person), ∃ (Q : Person), Loves P Q)
  :=

begin
  assume h, -- arrow intro
  
  -- break up h using exists elim
  -- 1. there is someone everyone loves
  -- 2. everyone loves someone
  cases h with lenny everyone_loves_lenny,
  
  assume bruce : Person, -- for-all intro
  apply exists.intro lenny _,
  exacts everyone_loves_lenny bruce,
end