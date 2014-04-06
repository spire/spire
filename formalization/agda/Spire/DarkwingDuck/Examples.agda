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
ℕR = record
  { P = End
  ; I = λ _ → End
  ; E = ℕE
  ; B = λ _ →
      End tt
    , Rec tt (End tt)
    , tt
  }

ℕ : Set
ℕ = Form ℕR

zero : ℕ
zero = inj ℕR zeroT

suc : ℕ → ℕ
suc = inj ℕR sucT

VecR : Data
VecR = record
  { P = Arg Set (λ _ → End)
  ; I = λ _ → Arg ℕ (λ _ → End)
  ; E = VecE
  ; B = λ A →
      End (zero , tt)
    , Arg ℕ (λ n → Arg (proj₁ A) λ _ → Rec (n , tt) (End (suc n , tt)))
    , tt
  }

Vec : (A : Set) → ℕ → Set
Vec = Form VecR

nil : {A : Set} → Vec A zero
nil = inj VecR nilT

cons : {A : Set} (n : ℕ) (x : A) (xs : Vec A n) → Vec A (suc n)
cons = inj VecR consT

----------------------------------------------------------------------

add : ℕ → ℕ → ℕ
add = elim ℕR (λ n → ℕ → ℕ)
  (λ n → n)
  (λ m ih n → suc (ih n))

mult : ℕ → ℕ → ℕ
mult = elim ℕR (λ n → ℕ → ℕ)
  (λ n → zero)
  (λ m ih n → add n (ih n))

append : {A : Set} (m : ℕ) (xs : Vec A m) (n : ℕ) (ys : Vec A n) → Vec A (add m n)
append {A} = elim VecR (λ m xs → (n : ℕ) (ys : Vec A n) → Vec A (add m n))
  (λ n ys → ys)
  (λ m x xs ih n ys → cons (add m n) x (ih n ys))

concat : {A : Set} (m n : ℕ) (xss : Vec (Vec A m) n) → Vec A (mult n m)
concat {A} m = elim VecR (λ n xss → Vec A (mult n m))
  nil
  (λ n xs xss ih → append m xs (mult n m) ih)

----------------------------------------------------------------------
