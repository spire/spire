open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality
module Spire.Examples.ComputationalDesc where

----------------------------------------------------------------------

data Desc (I : Set) : Set₁ where
  `⊤ : Desc I
  `X : (i : I) → Desc I
  `Σ `Π : (A : Set) (B : A → Desc I) → Desc I

El : (I : Set) (D : Desc I) (X : I → Set) → Set
El I `⊤ X = ⊤
El I (`X i) X = X i
El I (`Σ A B) X = Σ A (λ a → El I (B a) X)
El I (`Π A B) X = (a : A) → El I (B a) X

data μ (I : Set) (R : I → Desc I) (i : I) : Set where
  con : El I (R i) (μ I R) → μ I R i

All : (I : Set) (X : I → Set) (D : Desc I) (xs : El I D X) (P : (i : I) → X i → Set) → Set
All I X `⊤ tt P = ⊤
All I X (`X i) x P = P i x
All I X (`Σ A B) (a , b) P = All I X (B a) b P
All I X (`Π A B) f P = (a : A) → All I X (B a) (f a) P

----------------------------------------------------------------------

ind :
  (I : Set)
  (R : I → Desc I)
  (P : (i : I) → μ I R i → Set)
  (pcon : (i : I) (xs : El I (R i) (μ I R)) → All I (μ I R) (R i) xs P → P i (con xs))
  (i : I)
  (x : μ I R i)
  → P i x

hyps :
  (I : Set)
  (R : I → Desc I)
  (P : (i : I) → μ I R i → Set)
  (pcon : (i : I) (xs : El I (R i) (μ I R)) → All I (μ I R) (R i) xs P → P i (con xs))
  (D : Desc I)
  (xs : El I D (μ I R))
  → All I (μ I R) D xs P

ind I R P pcon i (con xs) = pcon i xs (hyps I R P pcon (R i) xs)

hyps I R P pcon `⊤ tt = tt
hyps I R P pcon (`X i) xs = ind I R P pcon i xs
hyps I R P pcon (`Σ A B) (a , b) = hyps I R P pcon (B a) b
hyps I R P pcon (`Π A B) f = λ a → hyps I R P pcon (B a) (f a)

----------------------------------------------------------------------

data ℕT : Set where `zero `suc : ℕT
data VecT : Set where `nil `cons : VecT

ℕD : ⊤ → Desc ⊤
ℕD tt = `Σ ℕT λ
  { `zero → `⊤
  ; `suc → `X tt
  }

ℕ : ⊤ → Set
ℕ = μ ⊤ ℕD

-- zero : ℕ tt
pattern zero = con (`zero , tt)

-- suc : ℕ tt → ℕ tt
pattern suc n = con (`suc , n)

----------------------------------------------------------------------

VecD : (A : Set) (n : ℕ tt) → Desc (ℕ tt)
VecD A zero = `⊤
VecD A (suc n) = `Σ A λ _ → `X n

Vec : (A : Set) (n : ℕ tt) → Set
Vec A n = μ (ℕ tt) (VecD A) n

nil : (A : Set) → Vec A zero
nil A = con tt

cons : (A : Set) (n : ℕ tt) (x : A) (xs : Vec A n) → Vec A (suc n)
cons A n x xs = con (x , xs)

----------------------------------------------------------------------

addC : (u : ⊤) (xs : El ⊤ (ℕD u) ℕ)
  (ih : All ⊤ ℕ (ℕD u) xs (λ u n → ℕ u → ℕ u))
  → ℕ u → ℕ u
addC tt (`zero , tt) tt n = n
addC tt (`suc , m) ih n = suc (ih n)

add : ℕ tt → ℕ tt → ℕ tt
add = ind ⊤ ℕD (λ _ _ → ℕ tt → ℕ tt) addC tt

multC : (u : ⊤) (xs : El ⊤ (ℕD u) ℕ)
  (ih : All ⊤ ℕ (ℕD u) xs (λ u n → ℕ u → ℕ u))
  → ℕ u → ℕ u
multC tt (`zero , tt) tt n = zero
multC tt (`suc , m) ih n = add n (ih n)

mult : ℕ tt → ℕ tt → ℕ tt
mult = ind ⊤ ℕD (λ _ _ → ℕ tt → ℕ tt) multC tt

appendC : (u : ⊤) (A : Set) (m : ℕ u) (xs : El (ℕ u) (VecD A m) (Vec A))
  (ih : All (ℕ u) (Vec A) (VecD A m) xs (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)))
  (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)
appendC tt A zero tt tt n ys = ys
appendC tt A (suc m) (x , xs) ih n ys = cons A (add m n) x (ih n ys)

append : (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n) 
append A = ind (ℕ tt) (VecD A) (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)) (appendC tt A)

concatC : (u : ⊤) (A : Set) (m n : ℕ u) (xss : El (ℕ u) (VecD (Vec A m) n) (Vec (Vec A m)))
  (ih : All (ℕ u) (Vec (Vec A m)) (VecD (Vec A m) n) xss (λ n xss → Vec A (mult n m)))
  → Vec A (mult n m)
concatC tt A m zero tt tt = nil A
concatC tt A m (suc n) (xs , xss) ih = append A m xs (mult n m) ih

concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Vec A (mult n m)
concat A m = ind (ℕ tt) (VecD (Vec A m)) (λ n xss → Vec A (mult n m)) (concatC tt A m)

----------------------------------------------------------------------
