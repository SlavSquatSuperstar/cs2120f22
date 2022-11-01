/-
Writng Functions in Lean
Tue 10/25/22
-/

-- properties of objects can be expressed as predicates
def isEven : ℕ → Prop :=
begin
assume n,
exact (n%2 = 0)
end

def isEven1 : ℕ → Prop := fun n, n % 2 = 0
def isEven2 : ℕ → Prop := λ n,   n % 2 = 0 

def my_bool_and : bool → bool → bool 
-- must list all cases
| tt tt := tt
| _ _ := ff -- wildcard

#eval my_bool_and tt tt
#eval my_bool_and tt ff
#eval my_bool_and ff tt
#eval my_bool_and ff ff

-- unit testing
example : my_bool_and tt tt = tt := rfl
example : my_bool_and tt ff = ff := rfl
example : my_bool_and ff tt = ff := rfl
example : my_bool_and ff ff = ff := rfl

def my_bool_or : bool → bool → bool 
| ff ff := ff
| _ _ := tt

#eval my_bool_or tt tt
#eval my_bool_or tt ff
#eval my_bool_or ff tt
#eval my_bool_or ff ff

def my_bool_not : bool → bool 
| tt := ff
| ff := tt

#eval my_bool_not tt
#eval my_bool_not ff

def my_bool_imp : bool → bool → bool 
| tt tt := tt
| tt ff := ff
| ff _ := tt

#eval my_bool_imp tt tt
#eval my_bool_imp tt ff
#eval my_bool_imp ff tt
#eval my_bool_imp ff ff

def factorial : ℕ → ℕ
| 0 := 1
| (n' + 1) := (n' + 1) * factorial n'

#eval factorial 0
#eval factorial 1
#eval factorial 2
#eval factorial 3
#eval factorial 4

-- polymorphism
def id_nat : ℕ → ℕ | n := n
def id_string : string → string | s := s
def id_bool : bool → bool | b := b

-- def id_T (T : Type) : T → T | t := t
-- def id_T : ∀ (T : Type), T → T | T t := t
-- #eval id_T ℕ 3

def id_T {T : Type} : T → T | t := t -- implicit type argument
#eval id_T 3

namespace my_types
  inductive empty : Type
  inductive unit : Type | star

  def unit_fun : unit → unit | u := u
  open unit
  #eval unit_fun star
end my_types