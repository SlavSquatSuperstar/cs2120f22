
/-
Eric Weng
Thur, 10/20/22

This is the CS2120 (Sullivan) midterm exam. 

The exam has 100 points total distributed over four
multi-part questions. There's an extra credit question
at the end. Points for each part are indicated.
-/

-- ****************** #1 [30 points] *******************

/- A. [5 points] 

Is it true in predicate logic that  
(false → true) ∧ (false → false)?

Answer: Yes. Usually we work with abstract propositions
and make conclusions with proofs instead of truth judgements.
However, false and true are still propositions and work with
our inference rules.

-/

/- B. [10 points] 

Give a formal proof by completing the 
following "example" in Lean, or state 
in English that there is no such proof.

-/

example : (false → true) ∧ (true → true) :=
begin
apply and.intro,

-- first implication
assume false,
exact false.elim,

-- second implication
assume true,
exact true,
end


/- C [15 points]. 

Give an English language proof of the proposition. 
Identify each inference rule you use at each point
in your argument. For example, at a certain point 
you might say something like this: By the ____ rule, 
it will suffice to show ____. Then you would go on
to show that what remains to be proved is valid. 


Answer: We start with (false → true) ∧ (true → true).

By and introduction, as long as we have a proof of
false → true and true → true, we can deduce a proof of
(false → true) ∧ (true → true).

For the first implication, by arrow-intro, we need to
assume a false and derive a proof of true. By false elimination,
we can conclude that anything follows.

For the second implication, again using arrow-intro,
we need to assume true. Since we already have a proof of the conclusion,
we can exit there.

-/


-- ****************** #2 [30 points] *******************


/- 
"Resolution" is an inference rule that we 
haven't talked about before. It's valid in
propositional, classical, and constructive
predicate logic. We will present the rule,
in both propositional and predicate logic,
and will ask you to prove that is's valid
in each case.


In propositional logic, the resolution rule 
is ¬P ∨ Q, P ⊢ Q. To check its validity, we 
can write it as (¬P ∨ Q) ∧ P → Q. Note: ∧ 
has higher precedence than →, so there are 
implicit parentheses around (¬P ∨ Q) ∧ P, 
making the overall proposition an implication.
-/


/- A. [5 points].

Give a brief English language explanation why this
inference rule makes sense: not a rigorous proof,
just an explanation of why Q has to be true under
the conditions give by the assumptions/premises.

Answer: The inference rule is (¬P ∨ Q) ∧ P → Q.

If we assume that (not P is true, or Q is true), and P is true,
then either:
- P is true, meaning the only way for (not P or Q) to be true
is if Q is true, which is the conclusion.
- P is false (not P is true), then the and operator evaluates to false
no matter what (not P or Q) is. Since anything follows from a false context,
we can conclude that Q is true.

-/


/- B. [5 points]

Prove that this inference rule is valid in
propositional logic by giving a truth table for it. 
We'll give you a start. Fill in the rows then state
how you know from the truth table that the overall
proposition is valid.

P   Q   (¬P ∨ Q)    (¬P ∨ Q) ∧ P    ((¬P ∨ Q) ∧ P) → Q
------------------------------------------------------
f   f   t           f               t
f   t   t           f               t
t   f   f           f               t
t   t   t           t               t


Statement: For all possible combinations of P and Q,
((¬P ∨ Q) ∧ P) → Q is true

-/


/- C. [10 points] 

Give a formal proof that the inference rule is 
valid in our constructive predicate logic. Fill
in a proof script here to construct your proof.
Hint: remember that the cases tactic applied to
a proof of a conjunction applied and.elim both
left and right, and when applied to a proof of 
a disjunction gives you two cases to consider,
where you need to show that the remining goal
is true in either case. 
-/

example : ∀ (P Q : Prop), (¬P ∨ Q) ∧ P → Q :=
begin
assume P Q,                 -- for-all introduction
assume h : (¬P ∨ Q) ∧ P,    -- arrow introduction

let np_or_q : ¬P ∨ Q := and.elim_left h,
let p : P := and.elim_right h,

apply or.elim np_or_q,      -- use case analysis on disjunct

    -- ¬P is true
    assume np : ¬P,
    let f := np p,
    -- P contradicts with ¬P -> anythig is true
    exact false.elim f,

    -- Q is true
    assume q: Q,
    exact q, -- P implies P
end


/- D. [10 points]

Give an informal (English) proof 
that the inference rule is valid in predicate logic. 
Name each inference rule you use in your reasoning.

Answer:
Our inference rule is (¬P ∨ Q) ∧ P → Q.

- First, we use for-all introduction and assume P and Q are
any arbitrary proposition.
- Also, to prove an implication, we can use arrow intro and
assume the premise (¬P ∨ Q) ∧ P.
- Next, we can use and elimination to obtain a proof of both
(¬P ∨ Q) and P.
- Then, we can use or elimination to examine two cases of (¬P ∨ Q):
    1. ¬P is true: this contradicts with our premise, where P is true,
    so we use false elimination to conlcude anything is true
    2. Q is true: this is the conclusion, and we can exit

-/


-- ****************** #3 [20 points] *******************


/- 
A. [10 points]. Write formally (in constructive logic) 
the proposition that, for any propositions P and Q, if 
P is equivalent to Q (iff), then if P is true, then Q
is true. Hint: put parentheses around your ↔ expression. 
-/

-- Don't try to write a proof here; just the proposition
def if_p_iff_q_then_if_also_p_then_q : Prop :=
    ∀ (P Q : Prop),
    (P ↔ Q) → P → Q


/-
B. [10 points]

Give *either* a precise, complete English
language proof that this proposition is valid, naming 
each inference you you use in your reasoning, *or* give 
a formal proof of it using Lean. You do not have to give
both.

Chosen: Formal proof
-/


/- Option #1: Informal proof:
N/A
-/


/-
Option #2: Formal proof. Reminders: the iff elim
rules are called iff.mp and iff.mpr in Lean; or you
can use "cases" to apply the two elimination rules 
to a proof of a bi-implication automatically.
-/

example : if_p_iff_q_then_if_also_p_then_q :=
begin
unfold if_p_iff_q_then_if_also_p_then_q,
assume P Q,             -- for-all intro

assume p_iff_q : P ↔ Q, -- arrow intro
assume p : P,           -- arrow intro

-- this seems to have the same effect
-- let p_imp_q : P → Q := iff.elim_left p_iff_q,
let p_imp_q : P → Q := iff.mp p_iff_q,
exact p_imp_q p,        -- apply P → Q to (p : P) to get (q : Q)

end


-- ****************** #4 [20 points] *******************

/- A. [10 points]

Suppose P is any proposition. In plain
English give a step by step explanation of how you would 
go about proving ¬P using proof *by negation*. 

Answer: To prove ¬P is true, we want to show that P → false.
1. First, we need to assume the premise, P.
2. Then, we will need to show this context leads to an impossibility
by obtaining a proof of false. Often, we will have some proof
elsewhere that ¬P is true, which we can apply to P.
3. Lastly, we can use not introduction on P → false to conclude ¬P

-/


/- B. [10 points] 

In plain English explain each step in a proof of P
*by contradiction*. Identify where a proof by negation 
(¬ introduction) occurs in the proof by contradiction. 
Explain what classical rule of inference you need to 
use to finish off such a proof. 

Answer: To prove P is true, we want to show that (¬P → false).
1. First, we need to assume the premise, ¬P.
2. Next, we will need to show this context leads to an impossibility
by obtaining a proof of false. Often, we will have some proof
elsewhere that P is true, which we can apply to ¬P. This is
essentially a proof of negation.
3. Then, we can use not introduction on ¬P → false to conclude ¬(¬P).
4. Lastly, we will use the law of excluded middle or not elimination
to reduce ¬(¬P) to P.

-/


/- Extra Credit [10 points for all three answers correct]

Suppose that "if it's sunny, it's hot, and also that if 
it's not sunny, it's hot. 


A. Is it hot in classical logic? 

Answer: 


B. Is it hot "constructively?" Briefly explain your answer.

Answer: 


C. Give a formal proof of your answer to the classical question. 
Use S and H as names to stand for the propositions, "it's sunny" 
and "it's hot," where S stands for "it's sunny" and H stands for
"it's hot."
-/

-- it's hot
example : ∀ (S H : Prop), (S → H) → (¬S → H) → H :=
begin
end

