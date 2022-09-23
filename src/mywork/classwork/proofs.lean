/-
Writing Proofs in Lean
Thur 9/22/22
-/

variable Person : Type -- define a type
variable plato: Person -- create an instance
variable isMortal: Person -> Prop -- define a proposition
variable everyoneIsMortal : ∀(p: Person), isMortal p -- define a proof
#check everyoneIsMortal plato -- prove that Plato is mortal