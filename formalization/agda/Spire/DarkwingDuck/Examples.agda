{-# OPTIONS --type-in-type --no-pattern-matching #-}
open import Spire.DarkwingDuck.Primitive
open import Spire.DarkwingDuck.Derived
module Spire.DarkwingDuck.Examples where

----------------------------------------------------------------------

NatN : Name
NatN = "Nat"

NatE : Enum
NatE = "zero" ∷ "suc" ∷ []

NatP : Params
NatP = Emp

NatI : Indices NatP
NatI = indices NatP Emp

NatC : Constructors NatE NatP NatI
NatC = constructors NatE NatP NatI 
  (End tt , Rec tt (End tt) , tt)

Nat : FORM NatP NatI
Nat = Form NatN NatE NatP NatI NatC

zero : Inj NatN NatE NatP NatI NatC here
zero = inj NatN NatE NatP NatI NatC here

suc : Inj NatN NatE NatP NatI NatC (there here)
suc = inj NatN NatE NatP NatI NatC (there here)

elimNat : Elim NatN NatE NatP NatI NatC
elimNat = elim NatN NatE NatP NatI NatC

----------------------------------------------------------------------

VecN : Name
VecN = "Vec"

VecE : Enum
VecE = "nil" ∷ "cons" ∷ []

VecP : Params
VecP = Ext Set λ _ → Emp

VecI : Indices VecP
VecI = indices VecP λ A → Ext Nat λ _ → Emp

VecC : Constructors VecE VecP VecI
VecC = constructors VecE VecP VecI λ A →
    End (zero , tt)
  , Arg Nat (λ n → Arg A λ _ → Rec (n , tt) (End (suc n , tt)))
  , tt

Vec : FORM VecP VecI
Vec = Form VecN VecE VecP VecI VecC

nil : Inj VecN VecE VecP VecI VecC here
nil = inj VecN VecE VecP VecI VecC here

cons : Inj VecN VecE VecP VecI VecC (there here)
cons = inj VecN VecE VecP VecI VecC (there here)

elimVec : Elim VecN VecE VecP VecI VecC
elimVec = elim VecN VecE VecP VecI VecC

----------------------------------------------------------------------

add : Nat → Nat → Nat
add = elimNat
  (λ n → Nat → Nat)
  (λ n → n)
  (λ m ih n → suc (ih n))

mult : Nat → Nat → Nat
mult = elimNat
  (λ n → Nat → Nat)
  (λ n → zero)
  (λ m ih n → add n (ih n))

append : (A : Set) (m n : Nat) (xs : Vec A m) (ys : Vec A n) → Vec A (add m n)
append A m n = elimVec A
  (λ m xs → (ys : Vec A n) → Vec A (add m n))
  (λ ys → ys)
  (λ m' x xs ih ys → cons A (add m' n) x (ih ys))
  m

concat : (A : Set) (m n : Nat) (xss : Vec (Vec A m) n) → Vec A (mult n m)
concat A m n = elimVec (Vec A m)
  (λ n xss → Vec A (mult n m))
  (nil A)
  (λ m' xs xss ih → append A m (mult m' m) xs ih)
  n

----------------------------------------------------------------------

one : Nat
one = suc zero

two : Nat
two = suc one

three : Nat
three = suc two

[1,2] : Vec Nat two
[1,2] = cons Nat one one (cons Nat zero two (nil Nat))

[3] : Vec Nat one
[3] = cons Nat zero three (nil Nat)

[1,2,3] : Vec Nat three
[1,2,3] = cons Nat two one (cons Nat one two (cons Nat zero three (nil Nat)))

test-append : [1,2,3] ≡ append Nat two one [1,2] [3]
test-append = refl

----------------------------------------------------------------------
