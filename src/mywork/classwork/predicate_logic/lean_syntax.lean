/-
Lean Syntax
Tue 10/13/22
-/

-- declare and assign variables
def x := 1
#eval x
def catchphrase := "Super easy, barely an inconvenience!"
#eval catchphrase
def proof_of_true: true := true.intro
#check proof_of_true

-- local variables
#eval let a := 5 in a
-- #eval a -- doesn't exist here

-- declare but don't assign varialbes
variable Person: Type
variable p: Person
-- variable p: ℕ -- no reassignment (immutable)
#check p


variables (Bob Dylan : Person)  -- two Person instances
variable Likes : Person → Person → Prop -- a 2 argument predicate
variable likes_bob_dylan : Likes Bob Dylan -- a proof of a proposition
#check likes_bob_dylan -- we know this is a prop, but not what the value is