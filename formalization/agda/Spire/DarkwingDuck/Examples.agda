{-# OPTIONS --type-in-type #-}
open import Spire.DarkwingDuck.Primitive
open import Spire.DarkwingDuck.Derived
module Spire.DarkwingDuck.Examples where

----------------------------------------------------------------------

ℕE : Enum
ℕE = "zero" ∷ "suc" ∷ []

VecE : Enum
VecE = "nil" ∷ "cons" ∷ []

ℕT : Set
ℕT = Tag ℕE

VecT : Set
VecT = Tag VecE

zeroT : ℕT
zeroT = here

sucT : ℕT
sucT = there here

nilT : VecT
nilT = here

consT : VecT
consT = there here

----------------------------------------------------------------------

ℕR : Data
ℕR = Decl ℕE End End
  (End tt , Rec tt (End tt) , tt)

ℕ : Set
ℕ = Form ℕR

zero : ℕ
zero = inj ℕR zeroT

suc : ℕ → ℕ
suc = inj ℕR sucT

VecR : Data
VecR = Decl VecE
  (Arg Set λ _ → End)
  (λ _ → Arg ℕ λ _ → End)
  (λ A →
    End (zero , tt)
  , IArg ℕ (λ n → Arg A λ _ → Rec (n , tt) (End (suc n , tt)))
  , tt
  )

Vec : (A : Set) → ℕ → Set
Vec = Form VecR

nil : {A : Set} → Vec A zero
nil = inj VecR nilT

cons : {A : Set} {n : ℕ} (x : A) (xs : Vec A n) → Vec A (suc n)
cons = inj VecR consT

----------------------------------------------------------------------

add : ℕ → ℕ → ℕ
add = elim ℕR
  (λ n → ℕ → ℕ)
  (λ n → n)
  (λ m ih n → suc (ih n))

mult : ℕ → ℕ → ℕ
mult = elim ℕR
  (λ n → ℕ → ℕ)
  (λ n → zero)
  (λ m ih n → add n (ih n))

append : {A : Set} {m n : ℕ} (xs : Vec A m) (ys : Vec A n) → Vec A (add m n)
append {A} {m} {n} = elim VecR
  (λ m xs → (ys : Vec A n) → Vec A (add m n))
  (λ ys → ys)
  (λ x xs ih ys → cons x (ih ys))
  m

concat : {A : Set} {m n : ℕ} (xss : Vec (Vec A m) n) → Vec A (mult n m)
concat {A} {m} {n} = elim VecR
  (λ n xss → Vec A (mult n m))
  nil
  (λ xs xss ih → append xs ih)
  n

----------------------------------------------------------------------

one : ℕ
one = suc zero

two : ℕ
two = suc one

three : ℕ
three = suc two

[1] : Vec ℕ one
[1] = cons one nil

[2,3] : Vec ℕ two
[2,3] = cons two (cons three nil)

[1,2,3] : Vec ℕ three
[1,2,3] = cons one (cons two (cons three nil))

test-append : [1,2,3] ≡ append [1] [2,3]
test-append = refl

----------------------------------------------------------------------
