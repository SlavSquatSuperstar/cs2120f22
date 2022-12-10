/-
Eric Weng (qgt7zm)
CS 2120 Homework 7
Fri 12/9/22
Sets and Relations Continued
-/

import data.set

/- #1

Formally prove that if there's an object, a, of some 
type, α, having some property (satisfying a predicate), 
P, then not every object of type α fails to have property, 
P. Add a brief comment before each line of your proof 
script to provide what amounts to the outline of a good
English language proof.
-/

example (α : Type) (P : α → Prop) : (∃ a, P a) → (¬(∀ x, ¬ P x)) :=
begin
assume given, -- arrow into, assume there is one object with a property
cases given with a pa, -- exists elim, there is an object, and it has a property

assume none_with_p, -- proof by negation, assume opposite of the conclusion
have f := none_with_p a, -- contradict the existence of a with (P a), with our assumption
-- "have" is same as "let" but expands the predicate
contradiction,
end


/- Extra credit. 

The converse of this proposition is clasically true. If
not every object lacks propery, P, then there must be some
object that has it. If you try to prove the converse in
our constructive logic, what happens? Show you work, and
then briefly but clearly explain exactly what goes wrong.
-/


/- #2

Consider the following binary relation, r, with domain
and co-domain both being ℕ. For each following question,
answer yes/no then briefly justify your answer.

( domain = ℕ, r = {(0,0),(1,1),(2,2)}, co-domain=ℕ )

A. Is this relation reflexive? 
No, a reflexive relationship needs to relate all values in the domain
to themselves, but the domain of definition for r is only (0, 1, 2).

B. Is this relation symmetric?
Yes, r works both ways. If we apply the r to first value in each pair, then
apply r to the output, we will end up where we started.

C. Is this relation transitive? 
Technically, yes. Whever r a b = r b c, then r a c. Because there are
no such occurrences (false → true), we can call r transitive.

D. Is this relation an equivalence relation?
No, an equivalence relation requires reflexive, symmetric
and transitive properties, and r is not reflexive.
-/


/- #3

A binary relation, r, is said to be *anti-symetric* 
if, for all values in its domain, a and b, if r a b 
and if r b a then a = b. Give an example of a familiar
arithmetic relation that's anti-symmetric, and briefly
explain why it's so.

The ≤ relation is anti-symmetric. If both a ≤ b
and b ≤ a are true, then a = b must be true. Likewise,
the ≥ relation is also anti-symmetric.
-/


/- #4

A binary relation, r, is said to be *asymmetric* if
whenever, for any a and b, if r a b then ¬ r b a. Be
careful to note that asymmetry and antisymmetry are
different properties.  Answer each of the following 
sub-questions. We give you a formal definition of
asymmetry.
-/

def is_asymmetric 
  {α : Type} 
  (r : α → α → Prop) : Prop 
  := ∀ (a b : α), r a b → ¬ r b a 

/- A.

Name a familar arithmetic relation that's asymmetric
and briefly explain why you think it's asymmetric.

Answer here:

The < relation is anti-symmetric. If a < b is true,
then ¬(b < a) is true (b < a is false). Likewise,
the > relation is also anti-symmetric.
-/

-- What happened to part B???

/- C: 

An object cannot be related to itself in an asymmetric
relation. First, complete the following informal proof
of this statement.

Proof: Assume α, r, and a are as given (and in particular
assume that r is asymmetric). Now assume r a a.

Answer here (rest of proof): 
1. Assume r is asymmetric: for any a and b, if r a b is true,
then r b a is not true
2. Assume r a a and apply statement #1 to a and b
3. The definition of asymmetric states: if r a a is true, then r a a is not true.
4. We've just deduced a contradiction!
-/

/- D.

Now prove a closely related proposition formally. 
Add a comment to each line of your formal proof 
so as to construct a good skeleton for a fluent 
English language proof.
-/

example
  (α : Type) 
  (r : α → α → Prop)
  (h : is_asymmetric r) :
¬ ∃ (a : α), r a a :=
begin
assume premise, -- proof by negation, assume opposite of premise
cases premise with a raa, -- exists elim, assume some a and r a a
unfold is_asymmetric at h,
let x := h a a, -- plug a and a into is_asymmetric to show r a a → ¬r a a
let y := x raa, -- arrow elim, apply our implies statement to r a a
contradiction, -- we've contradicted our premise
end


/- #5

Prove that equality on an inhabited (non-empty) type 
is not assymetric. In the following formalization we
assume there is a value (a : α), which establishes 
that α is inhabited.
-/

example (α : Type) (a : α): ¬ is_asymmetric (@eq α) :=
begin
assume asym, -- proof by negation
unfold is_asymmetric at asym,

let x := asym a a, -- elim for-all with a and a
let ref := eq.refl a, -- show a = a
let y := x ref, -- contrast a = a with a ≠ a
contradiction,
end

/- Extra credit: What exactly goes wrong in a formal 
proof if you drop the "inhabitedness" condition? Give
as much of a formal proof as you can then explain why
it can't be completed (if it can't!).
-/


/- #6

Two natural numbers, p and q, are said to be 
"equivalent mod m" if p % m = q % m, which makes
"equivalence mod m" a binary relation on natural
numbers. Here's a formal definition of this binary
relation on the natural numbers (given an m).
-/

def equiv_mod_m (m : ℕ) : ℕ → ℕ → Prop := 
  λ p q : ℕ, p % m = q % m

/-
Prove using Lean's definition of "equivalence" that 
equiv_mod_m is an equivalence relation for any natural
number, m. Here you'll also use Lean's definitions of
reflexive, symmetric, and transitive. They are as we
have covered in class. 
-/

example : ∀ m : ℕ, equivalence (equiv_mod_m m) :=
begin
assume m : ℕ,
unfold equivalence,
apply and.intro,
  -- reflexive
  unfold reflexive,
  assume x : ℕ, -- for-all intro
  unfold equiv_mod_m, -- we're done here!

apply and.intro,
  -- symmetric
  unfold symmetric,
  assume x y : ℕ, -- for-all intro
  unfold equiv_mod_m,
  assume premise,
  rw premise, -- rewrite the goal

  -- transitive
  unfold transitive,
  assume x y z : ℕ, -- for-all intro
  unfold equiv_mod_m,
  assume xy_mod_eq,
  assume yz_mod_eq,
  rw xy_mod_eq, -- substitute twice
  rw yz_mod_eq, -- hooray math!
end


/- #7

Consider the relation, tin_rel, that associates people 
with U.S. taxpayer id numbers, which we'll represent as 
natural numbers here. 

Assume this relation is single-valued. Which of the 
following properties does this relation have? Give
a very brief justification of each answer. Assume
the domain is all living persons, and the co-domain
is all natural numbers.

-- it's a function: yes since functions are single-valued by definition
-- it's total: no, because only US taxpayers (adults) may have TINs
-- it's injective: yes, because no two people may have the same tax ID
-- it's surjective (where the co-domain is all ℕ): no, not all ℕs are
ID numbers, and there are not infinite taxpayers
-- it's strictly partial: yes, non-Americans cannot have TINs
-- it's bijective: no, it must be both injective and surjective
-/


/- #8

Suppose r is the empty relation on the natural 
numbers. Which of the following properties does
it have? Explain each answer enough to show you
know why your answer is correct.

An empty relationship doesn't relate anything to anything (it relates nothing)
-- reflexive: no, it does not relate any natural numbers to themselves
-- symmetric: yes, it always inputs an empty set and outputs an empty set
-- transitive: yes, there are 0 out of 0 cases where if r a b and r b c, then r a c
-/


/- #9

Here's a formal definition of this empty relation.
That there are no constructors given here means there 
are no proofs, which is to say that no pair can be 
proved to be in this relation, so it must be empty.
-/

inductive empty_rel : ℕ → ℕ → Prop

/-
Formally state and prove you answer for each of the
three properties. That is, for each property assert
either that empty_rel does have it or does not have it, 
then prove your assertion. Include English-language 
comments on each line to give the essential elements 
of a good English language proof.
-/

example : ¬reflexive empty_rel :=
begin
unfold reflexive,
assume h, -- proof by negation, assume empty_rel is reflexive
let x := h 0, -- arrow elim, apply 0 to (empty_rel x x)
cases x, -- show empty_rel doesn't relate 0 to 0
end

example : symmetric empty_rel :=
begin
unfold symmetric,
assume a b: ℕ, -- for-all intro, assume arbitrary a and b
assume h, -- arrow intro, assume premise, empty_rel a b
cases h, -- there are no cases where empty_rel relates a to b, thus false elim
end

example : transitive empty_rel :=
begin
assume a b c : ℕ, -- for-all intro, assume arbitrary a b c
assume h k, -- arrow intro, assume premises
cases h, -- there are no cases where empty_rel relates a to b, thus false elim
-- cases k does the same thing
end


/- #10

A relation, r, is said to have the property of being 
a *partial order* if it's reflexive, anti-symmetric,
and transitive. Give a brief English language proof 
that the subset relation on the subsets of any set, 
S (of objects of some type), is a partial order. 

Proof:  

Suppose S is a set, with a ⊆ S and b ⊆ S subsets. Then,
1. Reflexive: All sets a are subsets of themselves, thus a ⊆ a
2. Anti-Symmetric: If a contains b and b contains a, then all elements x in a are in b,
and all elements y in b are in a. Thus a and b are equal; if a ⊆ b and b ⊆ a, then a = b.
3. Transitive: If b contains a, all elements x in a are in b. If c contains b, then all
elements y in b are in c. Since b in c, all elements x in a are also in c, thus
if a ⊆ b and b ⊆ c, then b ⊆ c.

QED.
-/


/- #11 

Finally we return again to DeMorgan's laws, but
now for sets. You'll recall that these "laws" as we
have seent them so far tell us how to distribute ¬  
over ∨ and over ∧. You will also recall that set
intersection (∩) is defined by the conjunction (∧) 
of the membership predicates, set union (∪) by the
disjunction (∨), and set complement (Sᶜ for a set,
S), by negation (¬). It makes sense to hypothesize 
that we can recast DeMorgan's laws in terms of the
distribution of complement over set union and set
intersection. Indeed we can. Your job is to state
and prove (formally) the first DeMorgan laws for 
sets, which states that the complement of a union
of any two sets equals the intersection of their 
complements.

Hint: To prove that two sets are equal, S = T, use
the ext tactic. It applies a bew axiom (called set 
extensionality) that states that to prove S = T it 
suffices to prove S ↔ T, viewing the sets as being
defined by their logical membership predicates. You
know how to handle bi-implications. The rest you 
can do by seeing "not," "and," and "or" in place 
of complement, conjunction, and disjuction, resp.  
-/

example 
  (α : Type) 
  (a b: set α) :
  (a ∪ b)ᶜ = aᶜ ∩ bᶜ := 
begin
ext, -- set extentionality
split, -- bi-implication

-- forward
assume n_a_or_b, -- arrow intro
apply and.intro,
  -- x ∈ aᶜ
  assume x_in_a, -- proof by negation
  let x : x ∈ (a ∪ b) := -- or intro left
    begin
    left,
    assumption,
    end,
  contradiction,

  -- x ∈ bᶜ
  assume x_in_b, -- proof by negation
  let x : x ∈ (a ∪ b) := -- or intro right
    begin
    right,
    assumption,
    end,
  contradiction,

-- reverse
assume na_and_nb, -- arrow intro
cases na_and_nb with na nb, -- or elim

assume a_or_b, -- proof by negation
cases a_or_b with x_in_a x_in_b, -- or elim
repeat {contradiction},
end

