/-
Set Theory
Tue 11/1/22
-/
import data.set

-- Sets are just predicates!

def isEven : ℕ → Prop :=
begin
assume n,
exact (n%2 = 0)
end

-- Set comprehension (list comprehension)
def evens : set ℕ := { n : ℕ | isEven n}
def evens' : set ℕ := { n : ℕ | isEven n} -- use a function
def evens'' : set ℕ := { n : ℕ | n % 2 = 0} -- or use a lambda

#check evens
#check isEven

#reduce evens
#reduce evens'
#reduce evens''
#reduce isEven
#reduce isEven 2 -- predicate/set application yields proposition
#reduce isEven 3

def strings5 := { s : string | s.length = 5 }
#reduce strings5 "Lean!"

-- prove something fits a set
example : "Lean!" ∈ strings5 :=
begin
unfold strings5,
show 5 = 5, -- reduce the predicate
exact rfl,
end

def set135 := { n : ℕ | n = 1 ∨ n = 3 ∨ n = 5 }
#reduce 1 ∈ set135
#reduce 2 ∈ set135

example : 5 ∈ set135 := -- same as (set135 5)
begin
show 5 = 1 ∨ 5 = 3 ∨ 5 = 5,
right, -- apply or intro
right,
exact rfl,
end

example : 4 ∉ set135 :=
begin
assume h,             -- assume 4 ∈ set135
cases h with hl hr,   -- case analysis
cases hl,             -- left side
cases hr with hm hr,  -- split right side
  cases hm,
  cases hr
end

def empty_set := { n : ℕ | false } -- Ø
def empty_set' (T : Type) := { t : T | false }
#reduce 1 ∈ empty_set
#reduce 0 ∈ empty_set

def allnats := { n : ℕ | true } -- universal set
#reduce 1 ∈ allnats
#reduce 0 ∈ allnats

-- implies: P → Q
-- subset: S ⊂ T (everything in S is in T)

def negation : bool → bool → Prop
| tt ff := true
| ff tt := true
| _ _ := false

example: ∀ (b1 b2 : bool), negation b1 b2 ↔ bnot b1 = b2 :=
begin
assume b1 b2,
apply iff.intro, -- split
-- forward implication
assume neg : negation b1 b2,

  cases b1, -- case analysis on b1 and b2
  cases b2,

  cases neg, -- ff ff
  exact rfl, -- ff tt

  cases b2, 
  exact rfl, -- tt ff
  cases neg, -- tt tt

-- reverse implication
assume neq : !b1 = b2,

  cases b1,
  cases b2,

  cases neq, -- !ff = ff
  unfold negation, -- !ff = tt

  cases neq, -- !tt = ff
  unfold negation,
end 

-- set "multiplication"
-- A * B = {a1*b1, a1*b2, …, a2*b1…}
-- There are 2^n subsets of a size size n

def slength (s : string) (l : ℕ) : Prop := s.length = l
