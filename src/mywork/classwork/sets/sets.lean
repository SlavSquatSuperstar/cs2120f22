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

example : 5 ∈ set135 :=
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