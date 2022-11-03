/-
Eric Weng
CS 2120 Quiz 1
Thur 9/29/22
-/

/-
#1: For each of the following questions give a yes/no answer 
and then a very brief explanation why that answer is correct.
To explain why your answer is correct, name the specific rule
of inference that tells you it's correct, or explain that 
there is no such valid inference rule.
-/

/-
#1A

If a ball, b, is round *and* b is also red, is b red?

A: yes/no: Yes

B: Why? And elimination right
- isRound b ∧ isRed b ⊢ isRed b


#1B

If flowers make you happy and chocolates make you happy,
and I give you flowers *or* I give you chocolates, will
you be happy?

A: yes/no: Yes

B: Why? Or elimination
flowers ∨ chocolates, flowers → happy, chocolates → happy ⊢ happy


#1C: If giraffes are just zebras in disguise, then the 
moon is made of green cheese?

A. yes/no: Yes

B. Why? False elimination (false implies false)
assuming all giraffes are zebras:
- case false:
- we cannot disprove that the moon is green cheese, so we conclude true


#1D. If x = y implies that 0 = 1, then is it true that
x ≠ y?

A. yes/no: Yes

B. Why? Definition of negation (x = y → false)
Since (0 = 1) is false, x = y → false
Since false has no proofs, then our assumption must be false (only false implies false)
Thus (x = y) is false or (x ≠ y) is true


#1E. If every zebra has stripes and Zoe is a Zebra then
Zoe has stripes.

A. yes/no: Yes

B. Why? For all elimination
(∀ (z: Zebra) → striped z) ⊢ (Zoe: Zebra) → striped Zoe


#1F. If Z could be *any* Zebra and Z has stripes, then 
*every* Zebra has stripes.

A. Yes/no: Yes

B: Why? For all-arrow equivalence
If Z is an arbitrary zebra and Z has stripes, then we can generalize and say
all zebras have stripes
(Z: Zebra), striped Z ↔ ∀ (z: Zebra) → striped z
**(For-all introduction is correct)**


#1G. If whenever the wind blows, the leaves move, and 
the leaves are moving, then the wind is blowing.

A. yes/no: No

B. Why? This is a converse logical fallacy
¬(wind → moving leaves ⊢ moving leaves → wind)
**(Affirming the conclusion is correct)**

If the leaves are moving, we cannot deduce the wind is blowing
because there may be other factors causing the leaves to move
that we do now know about.


#1H: If Gina is nice *or* Gina is tall, and Gina is nice,
then Gina is not tall. (The "or" here is understood to be
the or of predicate logic.)

A. yes/no: No

B. Why? This is affirming the disjunct, which is a logical fallacy
¬(isNice Gina ∨ isTall Gina, isNice Gina ⊢ ¬isTall Gina)

According to the truth table for or, "Gina is nice or Gina is tall" can be true if:
1. Gina is nice
2. Gina is tall
3. Gina is nice and and Gina is tall

Thus, knowing that Gina is nice tells us no information about whhether Gina is tall.
-/


/- 
#2

Consider the following formula/proposition in propositional
logic: X ∨ ¬Y.

#2A: Is is satisfiable? If so, give a model (a binding of 
the variables to values that makes the expressions true).

Yes. If X is true and Y is false, then true ∨ ¬false = true ∨ true = true
**(Y could be anything)**

#2B: Is it valid? Explain your answer. 

No. If X is false and Y is true, then false ∨ ¬ true = false ∨ false = false

-/


/-
#3: 

Express the following propositions in predicate logic, by
filling in the blank after the #check command.

If P and Q are arbitrary (any) propositions, then if (P is 
true if and only if Q is true) then if P is true then Q is 
true.
-/

#check ∀ (P Q: Prop), (P ↔ Q) → (P → Q)



/-
#4 Translate the following expressions into English.
The #check commands are just Lean commands and can
be ignored here. 
-/


-- A
#check ∀ (n m : ℕ), n < m → m - n > 0

/-
Answer: For all natural numbers n and m, if n is less then m,
then m - n is greater than 0.
-/

-- B

#check ∃ (n : ℕ), ∀ (m : ℕ), m >= n

/-
Answer: There exists a natural number n, for which all
natural numbers m are greater than or equal to n.
-/


-- C

variables (isEven: ℕ → Prop) (isOdd: ℕ → Prop)
#check ∀ (n : ℕ), isEven n ∨ isOdd n

/-
Answer: All natural numbers are even or odd.
-/


-- D

#check ∀ (P : Prop), P ∨ ¬P

/-
Answer: All propositions are true or false (excluded middle).
-/


-- E

#check ∀ (P : Prop), ¬(P ∧ ¬P)

/-
Answer: No propositions can be both true and false (no contradiction).
-/


/-
#5 Extra Credit

Next we define contagion as a proof of a slightly long
proposition. Everything before the comma introduces new
terms, which are then used after the comma to state the
main content of the proposition. 

Using the names we've given to the variables to infer
real-world meanings, state what the logic means in plain
natural English. Please don't just give a verbatim reading
of the formal logic. 
-/

variable contagion : 
  ∀ (Animal : Type) 
  (hasVirus : Animal → Prop) 
  (a1 a2 : Animal) 
  (hasVirus : Animal → Prop)
  (closeContact : Animal → Animal → Prop), 
  hasVirus a1 → closeContact a1 a2 → hasVirus a2


/-
Answer:
If animal a1 has a virus and has been in close contact with animal a2,
and a2 has the virus, then the virus is contagious.

**(Correct answer:)**
Contagion is a proof: if animal a1 has a virus and a2 comes into
touch with animal a2, then a2 will catch the virus.
-/