/-
Eric Weng (qgt7zm)
CS 2120 Homework 3
Thur 10/6/22
Predicate Logic

PURPOSE: The purpose of this homework is to help you understand
the material covered up to now on first- and higher-order predicate
logic. There are four questions. Each samples your understanding of
multiple concepts. You might have to put different ideas from our
work together to fully answer the questions. Give yourself time to
think about this material. 

INSTRUCTIONS: Read and follow the instructions for each question,
below. Edit all of your answers into this file. That's what you'll
turn in.

COLLABORATION: You may communicate with each other in general terms
about the material we've covered but you are NOT to give or receive
specific answers, or hints strong enough to essentially give away any 
answers, on this homework. Please, do yourselves and your colleagues
a favor and don't tell or take answers. This homework is a key check
on, and preparation for, an upcoming midterm exam.  

NEED HELP: Please don't post answers or partial answers on Piazza or 
any other forum that would substantially give away any part of the 
answer to any of these questions. That said, freely post any questions
you might have, and feel free to offer general answers to questions 
from others, on Piazza. Our TAs answer at least several times a day. 
Attend office hours: Wednesday and Sunday night 7-10. Talk to Sullivan. 
If you feel deeply lost, email Prof. Sullivan ASAP to for help on how
best to proceed. 

WHERE TO SUBMIT: Assignment tab for HW#3 on Collab
-/


/- #1: Logic to English 

Read through the new material in 09_20_22_inference_rules.lean, which
starts on line 264. After reviewing our all balls blue example, it then
presents an English-language rendition of our "demonstration" that if 
all balls are blue and if b1 and b2 are balls then b1 is blue and b2 
is blue. Compare the English language proof with the formal version, 
paying attention to how we named and specified the proof that all balls
are blue. 

Continue reading through our formalized version of the story that 
everyone is mortal and so is Socrates so Socrates is mortal. Now 
write an English-language version of the proof, using the model from 
the earlier case of "all balls blue." Don't just do it mindlessly: 
really think about what you're saying with each word in your proof. 
See how the English presents the "story" of the formal proof in more
natural, human, terms.

ANSWER HERE:

"Socrates is Mortal" in Logic:
  variable Person : Type
  variable Socrates : Person
  variable isMortal : Person → Prop
  variable everyoneIsMortal : ∀ (p : Person), isMortal p
  #check (everyoneIsMortal Socrates)

"Socrates is Mortal" in English:
  First, we consider a type, Person. We also conisder the predicate isMortal,
  which takes a Person object and asserts that single person is mortal.

  Next, we construct the proof everyoneIsMortal by accepting any arbitrary person
  (∀ (p : Person)), and claiming that individual is mortal (isMortal p). EveryoneIsMortal
  produces the claim that for all persons p, p is mortal.

  Lastly, we can define Socrates as an instance of Person. Since Socrates is an
  arbitrarily selected Person, we apply our previous generalization and deduce that
  Socrates is mortal.
-/


/- #2: English to Logic 
Formally model this natural-language "logic story" in Lean, using
the material we covered in the lecture notes as a model. Here's the
story.

If one person likes a second, and the second likes a third, 
then the first is jealous of the third. Furthermore, Ed, Hannah, 
and Mel are people; Ed likes Hannah; and Hannah likes Mel. 

Write, and use #check to check, an expression that proves that Ed 
is jealous of Mel. 
-/

-- ANSWER:
variable Person : Type
variable Likes : Person → Person → Prop
variable Jealous : Person → Person → Prop
variable Triangle : -- If p1 likes p2, and p2 likes p3, then p1 is jealous of p3
  ∀ (p1 p2 p3 : Person),
  Likes p1 p2 →
  Likes p2 p3 →
  Jealous p1 p3

variables ed hannah mel : Person
variable likes_ed_hannah : Likes ed hannah
variable likes_hannah_mel : Likes hannah mel

-- Finally write and use #check to check an expression that proves that ed is 
-- jealous of mel.
#check (Triangle ed hannah mel) likes_ed_hannah likes_hannah_mel
-- Provide "Ed likes Hannah" and "Hannah likes Mel" to the Triangle proposition


/- #3: Proofing a propositions involving ∀ and ∨

Write an English-language proof of the following proposition, using
the methods of inference we've covered: ∀ (P Q : Prop), P ∧ Q → Q ∨ P. 

Do read that proposition carefully, please. You don't need to write a
long proof. Keep it concise. Identify the inference rules you use.

ANSWER:

Given: (P and Q) is true
Prove: (Q or P) is true

1. For all propositions P and Q, if we have proof that if (P and Q) is true,
then by AND elimination right, we can deduce that Q is true.

2. Since Q is true, we can use OR introduction left to conclude that (Q or P) is true.
-/


/- #4: Modeling a logic story

Model the following logic story formally. Everyone knows someone who 
knows someone who knows everyone.
-/

-- ANSWER:
-- variable Person : Type
variable Knows : Person → Person → Prop

def answer : Prop :=
  -- Given
  ∀ (e1 e2 : Person),
  ∃ (s1 s2 : Person),

  -- Proof
  Knows e1 s1 ∧
  Knows s1 s2 ∧
  Knows s2 e2

  /- This is equivalent
  Knows e1 s1 →
  Knows s1 s2 →
  Knows s2 e2
  -/

#check answer