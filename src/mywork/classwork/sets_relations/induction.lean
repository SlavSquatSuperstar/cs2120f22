/-
Induction
Tue 11/29/22
-/

/-
Some functions are easy to define with finite cases
Sum(n) has infinite cases
Every inductive data type gives us an inductive axiom
-/

inductive boolean : Type
| false
| true
-- no other values of this type (enumerated)

def is_false : boolean → bool
| boolean.false := tt
| boolean.true  := ff

inductive integer : Type
| zero                          -- build the ground floot
| succ (n : integer) : integer  -- build the next floors
-- infinite values, unary notation

-- integer functions

def get_value : integer → ℕ
| integer.zero      := 0
| (integer.succ n)  := (get_value n) + 1

def increment (n : integer): integer := integer.succ n

def decrement : integer → integer -- pattern matching
| integer.zero      := integer.zero
| (integer.succ n)  := n

def add : integer → integer → integer
| n integer.zero      := n
| n (integer.succ m)  := integer.succ (add n m) -- n + (m + 1) = (n + m) + 1
-- iteratively apply succ to arg1, arg2 times

def mul : integer → integer → integer
| n integer.zero      := integer.zero
| n (integer.succ m)  := add n (mul n m) -- n * (m + 1) = (n * m) + n

def pow : integer → integer → integer
| n integer.zero      := integer.zero.succ
| n (integer.succ m)  := mul n (pow n m) -- n ^ (m + 1) = (n ^ m) * n

def fact : integer → integer
| integer.zero      := integer.zero.succ
| (integer.succ n)  := mul n.succ (fact n) -- n * (m + 1) = (n * m) + n

def fact' : integer → integer :=
begin
assume n : integer,
induction n with z n',
  -- n = 0
  exact integer.zero.succ,
  -- n = m + 1
  exact mul (n'.succ) (fact' n'),
end

-- testing our values

open integer
def one := succ zero
def two := succ one
def three := succ two
def four := succ three

#reduce zero
#reduce one
#reduce succ one
-- and so on…

-- calling our functions

#reduce get_value zero -- 0
#reduce get_value one -- 1
#reduce get_value two -- 2

#reduce get_value (increment zero) -- 0++
#reduce get_value (increment one) -- 1++
#reduce get_value (increment two) -- 2++

#reduce get_value (decrement zero) -- 0--
#reduce get_value (decrement one) -- 1--
#reduce get_value (decrement two) -- 2--

#reduce get_value (add one zero) -- 1 + 0
#reduce get_value (add one one) -- 1 + 1
#reduce get_value (add one two) -- 1 + 2

#reduce get_value (mul one zero) -- 1 * 0
#reduce get_value (mul one one) -- 1 * 1
#reduce get_value (mul one two) -- 1 * 2
#reduce get_value (mul four two) -- 4 * 2

#reduce get_value (pow zero two) -- 0 ^ 2
#reduce get_value (pow two zero) -- 2 ^ 0
#reduce get_value (pow one two) -- 1 ^ 1
#reduce get_value (pow two three) -- 2 ^ 3
#reduce get_value (pow four two) -- 4 ^ 2

#reduce get_value (fact zero) -- 0!
#reduce get_value (fact one) -- 1!
#reduce get_value (fact four) -- 4!

/-
Proof by induction

1. Show that the base case has a certain property
2. Show that the successor of any value has a certain property
-/

def is_chunky := ℕ → Prop