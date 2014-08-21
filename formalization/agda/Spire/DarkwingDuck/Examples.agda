{-# OPTIONS --type-in-type --no-pattern-matching #-}
open import Spire.DarkwingDuck.Primitive
open import Spire.DarkwingDuck.Derived
module Spire.DarkwingDuck.Examples where

----------------------------------------------------------------------

NatN : String
NatN = "Nat"

NatP : Tel
NatP = Emp

NatI : Scope NatP → Tel
NatI _ = Emp

NatE : Enum
NatE = "zero" ∷ "suc" ∷ []

NatB : (p : Scope NatP) → BranchesD NatE (NatI p)
NatB _ = End tt , Rec tt (End tt) , tt

Nat : Set
Nat = Form NatN NatP NatI NatE NatB

zero : Nat
zero = inj NatN NatP NatI NatE NatB here

suc : Nat → Nat
suc = inj NatN NatP NatI NatE NatB (there here)

elimNat : (P : Nat → Set)
  (pz : P zero)
  (ps : (n : Nat) → P n → P (suc n))
  (n : Nat) → P n
elimNat = elim NatN NatP NatI NatE NatB

----------------------------------------------------------------------

VecN : String
VecN = "Vec"

VecP : Tel
VecP = Ext Set λ _ → Emp

VecI : Scope VecP → Tel
VecI _ = Ext Nat λ _ → Emp

VecE : Enum
VecE = "nil" ∷ "cons" ∷ []

VecB : (p : Scope VecP) → BranchesD VecE (VecI p)
VecB = uncurryScope VecP (λ p → BranchesD VecE (VecI p)) λ A
  → End (zero , tt)
  , Arg Nat (λ n → Arg A λ _ → Rec (n , tt) (End (suc n , tt)))
  , tt

Vec : (A : Set) → Nat → Set
Vec = Form VecN VecP VecI VecE VecB

nil : (A : Set) → Vec A zero
nil = inj VecN VecP VecI VecE VecB here

cons : (A : Set) (n : Nat) (x : A) (xs : Vec A n) → Vec A (suc n)
cons = inj VecN VecP VecI VecE VecB (there here)

elimVec : (A : Set) (P : (n : Nat) → Vec A n → Set)
  (pn : P zero (nil A))
  (pc : (n : Nat) (x : A) (xs : Vec A n) → P n xs → P (suc n) (cons A n x xs))
  (n : Nat) (xs : Vec A n) → P n xs
elimVec = elim VecN VecP VecI VecE VecB

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
