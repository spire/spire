{-# OPTIONS --type-in-type --no-pattern-matching #-}
open import Spire.DarkwingDuck.Primitive
open import Spire.DarkwingDuck.Derived
module Spire.DarkwingDuck.Examples where

----------------------------------------------------------------------

ℕR : Data
ℕR = Decl "Nat" Emp Emp
  ("zero" ∷ "suc" ∷ [])
  (End tt , Rec tt (End tt) , tt)

ℕ : Set
ℕ = Form ℕR

zero : ℕ
zero = inj ℕR here

suc : ℕ → ℕ
suc = inj ℕR (there here)

VecR : Data
VecR = Decl "Vec"
  (Ext Set λ _ → Emp)
  (λ _ → Ext ℕ λ _ → Emp)
  ("nil" ∷ "cons" ∷ [])
  (λ A →
    End (zero , tt)
  , Arg ℕ (λ n → Arg A λ _ → Rec (n , tt) (End (suc n , tt)))
  , tt
  )

Vec : (A : Set) → ℕ → Set
Vec = Form VecR

nil : (A : Set) → Vec A zero
nil A = inj VecR A here

cons : (A : Set) (n : ℕ) (x : A) (xs : Vec A n) → Vec A (suc n)
cons A = inj VecR A (there here)

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

append : (A : Set) (m n : ℕ) (xs : Vec A m) (ys : Vec A n) → Vec A (add m n)
append A m n = elim VecR A
  (λ m xs → (ys : Vec A n) → Vec A (add m n))
  (λ ys → ys)
  (λ m' x xs ih ys → cons A (add m' n) x (ih ys))
  m

concat : (A : Set) (m n : ℕ) (xss : Vec (Vec A m) n) → Vec A (mult n m)
concat A m n = elim VecR (Vec A m)
  (λ n xss → Vec A (mult n m))
  (nil A)
  (λ m' xs xss ih → append A m (mult m' m) xs ih)
  n

----------------------------------------------------------------------

one : ℕ
one = suc zero

two : ℕ
two = suc one

three : ℕ
three = suc two

[1,2] : Vec ℕ two
[1,2] = cons ℕ one one (cons ℕ zero two (nil ℕ))

[3] : Vec ℕ one
[3] = cons ℕ zero three (nil ℕ)

[1,2,3] : Vec ℕ three
[1,2,3] = cons ℕ two one (cons ℕ one two (cons ℕ zero three (nil ℕ)))

test-append : [1,2,3] ≡ append ℕ two one [1,2] [3]
test-append = refl

----------------------------------------------------------------------
