/-
Eric Weng (qgt7zm)
CS 2120 Homework 5
Sun 11/6/22
Exists Inference Rules
-/

import tactic.ring

/-
This assignment has three multi-part problems.
The first two problems will develop and test 
your understanding of exists introduction; and 
the third, of exist elimination. Problems that
ask you to state and prove a proposition will
get half credit for a correct proposition and
the other half for a correct proof. 
-/


/- *** Exists introduction *** -/

/- #1A.

State and prove the proposition that there's some
natural number whose square is 144.
-/

example : ∃ (n : ℕ), n * n = 144 :=
begin
  let n : ℕ := 12,        -- witness
  apply exists.intro n,
  exact rfl,              -- proof witness satistfies proposition
end


/- #1B.

State and prove the proposition that there is 
some string, s, such that s ++ "!" is the string, 
"I love logic!". Note: In Lean, ++ is notation
for string.append, the function for gluing two
strings together into one.
-/

example : ∃ (s : string), s ++ "!" = "I love logic!" :=
exists.intro "I love logic" rfl
-- same as this
-- begin
--   apply exists.intro "I love logic",
--   exact rfl,
-- end


/- #1C.

Formally state and prove the proposition that
there are three natural numbers, x, y, and z, 
such that x*x + y*y = z*z. Hint: exists.intro
takes just one witness as a time, so you will
have to apply it more than once.
-/

example : ∃ (x y z : ℕ),
  x*x + y*y = z*z :=
begin
  apply exists.intro 3,
  apply exists.intro 4,
  apply exists.intro 5,   -- three witnesses this time
  exact rfl,
end


/- #1D

Define predicate called pythag_triple taking
three natural number arguments, x, y, and z,
yielding the proposition that x*x + y*y = z*z.
-/

def pythag_triple (x y z : ℕ) := x*x + y*y = z*z

#reduce pythag_triple 3 4 5
#reduce pythag_triple 1 2 3


/- #1E

State the proposition that there exist x, y, z, 
natural numbers, that satisfy the pythag_triple, 
predicate, then prove it. (Use "example : ...")
-/

example : ∃ (x y z : ℕ),
  pythag_triple x y z :=
begin
  apply exists.intro 3,
  apply exists.intro 4,
  apply exists.intro 5,
  exact rfl,
end


/- #2A

Define a predicate, (multiple_of n m), where
n and m are natural numbers and where the
proposition is true if and only if n is a 
multiple of m. Hint: What has to be true for 
n to be a multiple of m? There has to be some
other number involved, right?
-/

def multiple_of (n m : ℕ) := ∃ (k : ℕ), n = m * k

#reduce multiple_of 10 5


/- #2B

Using the predicate multiple_of, state and 
prove the proposition that every natural number 
that is a multiple of 6 is also a multiple of 3. 

(Ring explanation abridged for the sake of brevity)

Ok, with that background in place, let's 
return to the problem we were discussing. 
Is it true that if any natural number is
a multiple of 6 then it's also a multiple 
of 3?

Before you even consider writing a proof, 
whether in Lean or in English, figure out 
yourself whether the proposition appears to 
be true or not. Try to prove it "mentally"
to yourself first. 

The key question here is, what does it even 
mean for a number, n, to be a multiple of 6. 
Well, n is a multiple of 6 if there's some 
number, say k, such that n = k * 6, right? 

Now you should be able to formally write, and 
then prove, the proposition on the table. Is 
it true that for any n, if n is a multiple of 
6 then it's a multiple of 3? 

What would it mean to be a multiple of 3? It
means there's some *other* number such that n
is that number times 3. The trick to this kind
of question is to figure out what that number
has to be. Also, be sure to use multiple_of in
formally stating the proposition to be proved.
-/

-- "For any n, if n multiple of 6, then n multiple of 3"
example : ∀ (n : ℕ), (multiple_of n 6) → (multiple_of n 3) :=
begin
  assume n : ℕ,
  assume mult_n6 : multiple_of n 6,

  -- There is a k where n = k * 6
  unfold multiple_of at mult_n6,
  cases mult_n6 with k mult_nk, -- use exists elim

  -- Prove that n = 2k * 3
  apply exists.intro (2 * k), -- supply the witness
  ring_nf, -- lean prefers ring_nf over ring 
  assumption, -- we have the conclusion
end 


/- #2C.

Is it true that if n is a multiple of h, and h
is a multiple of k, that n is a multiple of k? 
Formally state and then prove the proposition.

(Rewrite explanation abridged)
-/

-- if multiple_of n h, and multiple_of h k, then multiple_of n k
example (a b c : ℕ) :
∀(a b c), (multiple_of a b) ∧ (multiple_of b c) → (multiple_of a c)
:=
begin
assume a b c,
assume given,

cases given with mult_ab mult_bc, -- and elim
unfold multiple_of at mult_ab mult_bc,

cases mult_ab with k mult_ak, -- a = k * b
cases mult_bc with l mult_bl, -- b = l * c

rw mult_ak, -- substitute
rw mult_bl, 
-- proof reduced to a = k * l * c
apply exists.intro (l * k),
ring, -- multiplication is associative
end


/- *** exists.elimination *** -/

/- #3A

Formally state and prove that if everyone 
who knows logic is cool and someone knows 
logic, then *someone is cool*. We set up 
everything you need to formally state this
conclusion (first hole/underscore). All 
you then have to do is to fill in is the
proof (second _).
-/

example 
  (Person : Type)
  (KnowsLogic : Person → Prop)
  (isCool : Person → Prop)

  (LogicMakesCool : ∀ (p), KnowsLogic p → isCool p)
  (SomeoneKnowsLogic : ∃ (p), KnowsLogic p) :
  
  ∃(p : Person), isCool p :=
begin
cases SomeoneKnowsLogic with w knowsLogicW, -- use exists elim
apply exists.intro w, -- supply witness
-- prove isCool w
exact LogicMakesCool w knowsLogicW, -- predicate application

-- same as above
-- exact exists.intro w (LogicMakesCool w knowsLogicW)
end


/- #3B

Formally state and prove the proposition that if
someone is not happy then not everyone is happy.
-/

example 
  (Person : Type)
  (Happy : Person → Prop) :
  (∃ (p : Person), ¬Happy p) → ¬(∀ (q : Person), Happy q)
  -- ∃ (p : Person), ¬(Happy p) → ¬(∀ (q : Person), (Happy q))
  :=
begin
  assume one_unhappy,
  cases one_unhappy with p unhappy_p,
  -- proof by negation
  assume all_happy,
  let happy_p := all_happy p, -- prove p is happy
  contradiction,
end


/- #3C

Formally state and prove that  
"everyone is happy" is *equivalent*
(iff) to "no one is unhappy." 

Hint: In one direction, you might need 
to use classical reasoning; and remember
you can get a proposition (on which to do
classical case anaysis) by applying a
predicate to the right arguments. And
a final hint: Sometimes you have to use
information you have to prove something 
you don't yet have in order to make it
clear that there's a contradiction in
your set of assumptions. 
-/

example 
  (α : Type)
  (P : α → Prop) :
  (∀ (a : α), P a) ↔ ¬(∃ (b : α), ¬P b) :=
begin
  split,
  -- forward
  assume all_happy,
  assume one_unhappy,
  cases one_unhappy with w w_unhappy, -- someone; someone is unhappy
  let w_happy := all_happy w, -- prove someone is happy
  contradiction,

  -- reverse
  assume none_unhappy,
  assume a, -- someone

  -- prove there is someone happy
  let a_happy := P a, -- someone is unhappy
  cases classical.em a_happy with happy unhappy,
    -- P a
    assumption,

    -- ¬P a
    -- there is someone unhappy
    let f : false := none_unhappy (exists.intro a unhappy),
    contradiction,

end 


/- #3D

Formally state and prove the proposition
that if there doesn't exist an object of
some type T with some property, P, then
any object of that type has the property
¬P. Hint: We represent a "property" of 
objects of a certain type as a predicate
taking objects of that type.
-/

example 
  (T : Type)
  (P : T → Prop) :
  ¬(∃(t : T), P t) → (∀(u : T), ¬P u) :=
  -- If no t has P, then all t have ¬P
begin
  assume none_with_p,
  assume u : T,
  -- ¬P u by contradiction
  assume p_u : P u,
  cases classical.em (P u) with pu npu,
    -- P u
    let f := none_with_p (exists.intro u pu),
    assumption,
    -- ¬P u
    contradiction,

end


/- #3E

Formally state and prove the proposition
that if there's an object with the property 
of having property P or property Q then 
there's an object with property P or there's 
an object with property with property Q.
-/

example 
  (α : Type)
  (P : α → Prop)
  (Q : α → Prop) :
  (∃(a : α), P a ∨ Q a) →
  (∃(b : α), P b) ∨ (∃(c : α), Q c) :=
begin
  assume given,
  cases given with a pa_qa, -- exists elim
  cases pa_qa with pa qa, -- or elim
    -- P a
    apply or.inl,
    exact exists.intro a pa,
    -- Q a
    apply or.inr,
    exact exists.intro a qa,
end