/-
Eric Weng
Sat, 12/10/22
CS 2120 Final
-/

import data.set
import logic.relation


/- ****** -/
/-   #1   -/
/- ****** -/

/- A [5 points].

Give a formal definition of the proposition
that for every natural number, n, there's a
natural number, m, that's one more than n.
Replace the _ placeholder with your answer.
We will call your proposition prop1.
-/

def prop1 : Prop := ∀(n : ℕ), ∃(m : ℕ), m = n + 1


/- B [5 points].

Give a formal proof of this proposition. Include
a brief one line comment just before each line in 
your proof script explaining in English what it
does.
-/

example : prop1 :=
begin
unfold prop1, -- prove for all n, there is an m where m = n + 1
assume n : ℕ, -- for-all intro, assume an arbitrary ℕ, n

let m : ℕ := n + 1, -- define the successor of n, n + 1
apply exists.intro m, -- apply exists intro to n + 1 (witness)
exact rfl, -- show that n + 1 = n + 1, which satisfies the prop

/- Tried to prove by induction. Didn't need to!
induction n with zero n', -- proof by induction
  -- base case, 0
  apply exists.intro 1, -- exists intro
  exact rfl, -- show that 1 = 0 + 1

  -- inductive case, n'
  let succ_n : ℕ := n'.succ,
  -- forgeting the syntax, but use exists.intro with n' + 1
  apply exists.intro succ_n,
  exact rfl, -- show that m = n + 1
-/
end


/- #C [5 points].

Write a brief English language proof of prop1.

Answer: Assume n is an arbitrary ℕ, and show that
there is one larger number. The ℕ n + 1,
satisfies this property.

(The answer was already filled in...)
-/



/- ****** -/
/-   #2   -/
/- ****** -/

/-
We start by defining two "enumerated" data types, 
each with three values. We'll call them "lets" and
"nums," short for letters and numbers. The letters
are A, B, and C; and the numberrs are one, two, and
three.
-/

inductive lets : Type
| A
| B
| C

inductive nums : Type
| one
| two
| three

open lets nums


/- #A [5 points]

Define a function, l2n_ni (short for "letters to
numbers, not injective") using "by cases" syntax,
where l2n_ni is not injective. We don't care what
non-injective function you define, as long as it
is not injective. In a brief comment afterwards,
explain what makes it not injective.
-/

def l2n_ni : lets → nums
| A := one
| B := one
| C := three

/-
Answer (what makes it non-injective?):
An injective function is not many-to-one, which means
if f(a) = f(b), then a = b. Since l2n_ni outputs one
for both A and B, and A ≠ B, it is not injective.
-/


/- #B [5 points]

Define a function, l2n_s (short for "letters to
numbers, surjective") using "by cases" syntax,
where l2n_s is surjective. We don't care what
surjective function you define. 
-/

def l2n_s : lets → nums
| A := one
| B := two
| C := three


/- #C [5 points] 

Write a brief English-language proof showing that
your function is surjective. You must cite what it
means to be surjective (be mathematically precise).
Hint: You'll have to assume you're given any letter
as input. What you do with that arbitrary value to
complete the proof is the question to answer. Once
you have that, the rest is pretty straightforward.

Answer: A surjective function is one whose output (range)
covers its entire co-domain. In this case, for any
arbritrary letter (A, B, or C), we can show that the
possible outputs are either equal to one, two, or three.
We can accomplish the above by just plugging all values of
"lets" into l2n_s and showing the range covers all the
enumerated values of "nums".
-/


/- # EXTRA CREDIT [5 points] 

Prove formally that l2n_s is surjective.
-/
open function

lemma l2n_s_surjective: surjective l2n_s :=
begin
rw surjective,
assume n : nums, -- for-all intro, assume an arbritrary nums

-- show that all values in the co-domain
-- are achievable through any input
cases n with one two three,
  -- if output is one
  apply exists.intro A,
  exact rfl,
  -- if output is two
  apply exists.intro B,
  exact rfl,
  -- if output is three
  apply exists.intro C,
  exact rfl,
end



/- ****** -/
/-   #3   -/
/- ****** -/


/- #A [5 points] 

Write a formal definition of the predicate,
"is_even," taking a single natural number, n,
and reducing to the proposition that n mod 2
is 0. When you have it right, the first test
should pass, the second, fail, the third pass,
etc. 
-/

-- Answer:

def is_even : ℕ → Prop
| n := n % 2 = 0

-- tests
example : is_even 0 := rfl    -- even
example : is_even 1 := rfl    -- not even
example : is_even 2 := rfl    -- even
example : is_even 3 := rfl    -- not even
example : is_even 4 := rfl    -- even
example : is_even 5 := rfl    -- not even


/- #B [5 points]

Next, use set builder (comprehension) notation
to define the set of all even numbers, using
is_even as a "membership" predicate.
-/

def evens : set ℕ := {n : ℕ | is_even n}

/-
The next few problems use the following 
set.
-/

def under5 : set ℕ := {0, 1, 2, 3, 4, 5}


/- #C [5 points]

Prove: 2 ∈ evens ∩ under5. Hint: remember
wjat ∩ means logically, then use the right
logical inference rule. If you can't give
a formal proof, give a precise English
language proof instead, being precise
about the reasoning steps.
-/

example : 2 ∈ evens ∩ under5 :=
begin
apply and.intro, -- show that 2 ∈ evens ∧ 2 ∈ under5
  -- 2 ∈ evens
  exact rfl, -- show that 2 % 2 = 0

  -- 2 ∈ under5
  right,
  right,
  left, -- show that 2 = 2
  exact rfl,
end 

-- Alternative answer:


/- D [5 points]

Consider the set, justA = { A }, of 
"lets" (letters) as (defined above). 
-/

def just_A : set lets := { A } 

/-
Prove that (the letter) C is in 
just_Aᶜ, the complement of just_A. 
If you have problems getting Lean to
check your proof, you may give an 
English language version, instead,
but be sure to state *exactly* what 
(C ∈ just_Aᶜ) means and each reasoning 
step in your informal proof.
-/

example : C ∈ just_Aᶜ := 
begin
assume in_A, -- prove C ∉ just_A by negation, assume C ∈ A
cases in_A, -- show C = A, which is a contradiction
end

-- Alternative answer: 

/-
Proof: 
-/


/- E [5 points]

How many subsets are there of 
each of the following sets? You can
give an approximate answer on #4. 
Hint on 5: Recall that 𝒫 S means
the powerset of a set, S. So on
question 5, we are asking how many
subsets are there of the powerset 
of {0,1,2}.


                          Answers
1. {}                     1
2. {0,1,2}                2^3 = 8
3. {0,1,2,3,4,5,6,7,8,9}  2^10 = 1024
4. { n | 0 ≤ n ∧ n < 30}  2^30
- there would be 30 ℕs in this range
5. 𝒫 {0,1,2}              3*2^3 = 24
- 1 empty set -> 1
- 3 sets of 1 -> 3*2^1 = 3
- 3 sets of 2 -> 3^2^2 = 12
- 1 set of 3 -> 2^3 = 8
- 1 + 3 + 12 + 8 = 24
-/



/- ****** -/
/-   #4   -/
/- ****** -/


/- A [5 points]

Define a function, prod_to: ℕ → ℕ, that,
when applied to a given n returns: 1 if n
is zero; and otherwise (if n = succ n' for 
some n') the product of n and prod_to n'. 
You likely have it right when the tests all
pass.
-/

def prod_to : ℕ → ℕ 
| nat.zero := nat.zero.succ
| (nat.succ n') := (nat.succ n') * (prod_to n')

example : prod_to 0 = 1 := rfl
example : prod_to 1 = 1 := rfl
example : prod_to 2 = 2 := rfl
example : prod_to 3 = 6 := rfl
example : prod_to 4 = 24 := rfl


/- #B [5 points]

What is the common name of this function?

Answer: Factorial (n!)
-/


-- Problem 4C removed from exam, by professor's instruction
-- /- #C [5 points]

-- Give a brief explanation *why* proving these
-- two "lemmas" proves that the given property 
-- holds for *every* natural number. 

-- Answer: Natural numbers can be defined inductively,
-- with a base case 0 and a successor case n'+1.
-- If we define prod_to for the zero case and the
-- successor base, we have thus defined the function
-- inductively and shown how to get an output for
-- all ℕ values.
-- -/


/- #D [5 points]

This question tests your understanding of
the induction axiom for natural numbers.

You've learned that there are 2^n possible
"interpretations" of n propositional (i.e.,
Boolean) variables. Now *prove* that this 
is true. We'll help a bit. You fill in the
missing parts. 

1. The property, P, of n, we want to prove 
is that "the number of interpretations of 
a collection of n Boolean variables is 2^n." 

2. What we then want to prove is ∀ n, P nn

3. What specific proposition do we want
to prove as the "base case" in a proof by
induction? Be mathematically precise.

Answer: Since the base case for ℕ is 0, or nat.zero,
the base case of our proof is the number of
interpretations of 0 booleans is 2^0 = 1.

4. What specific proposition do we want to
prove as the "inductive case" in a proof by
induction? Be mathematically precise.

Answer: Since the inductive case for ℕ is, n'+1,
or nat.succ, the inductive case of our proof is
the number of interpretations of n'+1 booleans
is 2^(n+1) = 2*2^n, or double the interpretations
for a collection of n booleans.

5. Which expression in your preceding answer
corresponds to the induction hypothesis?

Answer: The "n'+1" corresponds to the induction hypothesis,
wherein proofs are made using the proofs of previous values,
this eventually lead to the base value.
-/



/- ****** -/
/-   #5   -/
/- ****** -/


/- #A [5 points] 

Prove the following formally. 
-/

example : ∀ (P Q : Prop), P ∧ Q → P ∨ Q :=
begin
assume P Q : Prop,
assume pq,
-- prove P and Q using and elim
let p := and.elim_left pq,
let q := and.elim_right pq,

-- prove P or Q using or intro
exact or.inl p,
-- exact or.inr q, -- this does the same thing
end


/- #B [5 points] 

Prove the following formally, writing
a brief comment before each line of your
proof script describing the logical step
it implements. Then below the formal proof
give an English-language version of it.
If the second half of the proof uses the
same strategy as the first half, you can,
in English, say, "the rest of the proof
uses the same strategy," and be done.
-/

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P :=
begin
assume P Q : Prop, -- for-all intro, assume arbitrary P Q
split, -- iff intro, prove one-way implications
  -- forward
  assume p_or_q, -- arrow intro, assume the premise
  cases p_or_q with p q, -- use or elim (cases) to get P or Q
    -- use or intro to prove conclusion for both cases
    -- prove Q ∨ P if P
    exact or.inr p,
    -- prove Q ∨ P if Q
    exact or.inl q,

  -- reverse
  assume q_or_p, -- arrow intro, assume the premise
  cases q_or_p with q p, -- use or elim (cases) to get P or Q
    -- use or intro to prove conclusion for both cases
    -- prove P ∨ Q if Q
    exact or.inr q,
    -- prove P ∨ Q if P
    exact or.inl p,
end

/-
Proof:

1. To prove a bi-implication, it suffices to prove
both one-way implications are true.
2. For the forward implication (P ∨ Q → Q ∨ P), we will
use arrow intro and assume the premise P ∨ Q.
3. From or elim (cases), we can derive P is true or Q is true.
4. Looking at each case:
a) If P is true, we can use or intro right on P to prove Q ∨ P.
b) If Q is true, we can use or intro left on Q to prove Q ∨ P.
5. The rest of the proof, the reverse implication (Q ∨ P → P ∨ Q),
uses the same strategy.
-/



/- ***************** -/
/-    EXTRA CREDIT   -/
/- ***************** -/

/-
We define a new polymorphic data type, 
tree. A tree is either a "twig" that 
carries a value of some type α; or a 
tree is a "root" that carries a value 
of type α and two "children,"" each 
itself such a tree. The definition is
polymorphic in the sense that values
in the tree can be of any type, α.
-/

inductive tree (α : Type)
| twig (a : α) : tree
| root (a : α) (left right : tree) : tree

open tree

/- #A 

Define a tree, t, of natural numbers, with 0 
at the root and two sub-trees: the left is a 
twig with the value 1, and the right is a twig
with the value 2. Here's a diagram:

          0     -- root with 0 and two sub-trees
         / \
        1   2   -- twigs with 1, 2; no sub-trees
-/

def t : tree nat :=
  (root 0) (twig 1) (twig 2)


/- #B

Define a function, tree_size, that takes any
tree and returns the number of values stored 
in it. For example, t stores three values (0,
1, and 2). Reminder: Put patterns in parens.
Answer by completing the partial definition 
we provide.
-/

def tree_size {α : Type} : tree α → ℕ  
| (twig v) := 1
| (root v l r) := 1 + (tree_size l) + (tree_size r)
-- count this node plus the sizes of the twigs

-- test cases
example : tree_size (twig 0) = 1 := rfl
example : tree_size t = 3 := rfl


/- #C 

Here's the induction axiom for the
tree type.
-/

#check @tree.rec_on

/-
tree.rec_on :
  Π {α : Type} 
  {motive : tree α → Sort u_1} 
  (n : tree α),
    (Π (a : α), motive (twig a)) →
    (Π (a : α) 
      (left right : tree α), 
      motive left → 
      motive right → 
      motive (root a left right)) → 
    motive n

Explain in English exactly how you'd prove, by
induction, that every tree has some property P. 
Be sure to explain what specific "lemmas" have to
be proved to complete the application of the
induction axiom for tree.

Answer: 
1. Base case: If the tree is a twig (no children), then
simply prove that the twig has property P (i.e. P twig)
2. Inductive case: If the tree is a root (two children),
then prove that the root and both its subtrees have property P
(i.e. P root ∧ P left ∧ P right).
-/

-- Thanks for a great semester, and have a good winter break!
