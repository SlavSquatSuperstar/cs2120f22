/-
Writing Proofs in Lean
Thur 9/22/22
-/

variable Person : Type -- define a type
variable plato: Person -- create an instance
variable isMortal: Person -> Prop -- define a proposition
variable everyoneIsMortal : ∀(p: Person), isMortal p -- define a proof
#check everyoneIsMortal plato -- prove that Plato is mortal (apply a proof to a particular object)

/-
Suppose you know that (X → Z) and (Y → Z) are true and you 
want to prove Z. To be able to prove Z it will *suffice* to 
prove X ∨ Y; for then you will need only to apply the or elim
rule to deduce that Z is true.

Suppose you know that (X → Z), (Y → Z), and Z are all true.
Is it necessarily that case that (X ∨ Y) is also true? No, because
maybe (W → Z) and W are also true, but we don't know in this context.
-/

/-
First-order logic. I know that every natural number is
beautiful (∀ n, NaturalNumber(n) → Beautiful(n) : true), 
and I want to prove (7 is beautiful : true). Prove it.
Name the inference rule and identify the arguments you
give it to prove it.

Use for-all elimination

Constructive logic. Suppose I have a proof, pf, that every 
natural number is beautiful (∀ (n : ℕ), beautiful n), and I 
need a proof that 7 is beautiful. How can I get the proof 
I need? Answer in both English and with a Lean expression

We apply a generaliztion of all ℕ to 7. First, prove 7 is a ℕ.
Then apply for-all elimination: since 7 is an arbitrary ℕ, we
conclude that 7 is beautiful.
-/
variable NatNum: Type
variable seven: NatNum
variable isBeautiful: NatNum -> Prop
variable allNatNumBeautiful : ∀(p: NatNum), isBeautiful p
#check allNatNumBeautiful seven