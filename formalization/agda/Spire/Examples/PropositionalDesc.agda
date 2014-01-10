open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality
module Spire.Examples.PropositionalDesc where

----------------------------------------------------------------------

data Desc (I : Set) : Set₁ where
  `Rec : (i : I) (D : Desc I) → Desc I
  `End : (i : I) → Desc I
  `Σ `Π : (A : Set) (B : A → Desc I) → Desc I

ISet : Set → Set₁
ISet I = I → Set

El : (I : Set) (D : Desc I) (X : ISet I) → ISet I
El I (`End j)   X i = i ≡ j
El I (`Rec j D) X i = X j × El I D X i
El I (`Σ A B)   X i = Σ A (λ a → El I (B a) X i)
El I (`Π A B)   X i = (a : A) → El I (B a) X i

data μ (I : Set) (D : Desc I) (i : I) : Set where
  con : El I D (μ I D) i → μ I D i

All : (I : Set) (D : Desc I) (X : ISet I) (P : (i : I) → X i → Set) (i : I) (xs : El I D X i) → Set
All I (`Rec j D) X P i (x , xs) = P j x × All I D X P i xs
All I (`End j) X P i q = ⊤
All I (`Σ A B) X P i (a , b) = All I (B a) X P i b
All I (`Π A B) X P i f = (a : A) → All I (B a) X P i (f a)

----------------------------------------------------------------------

ind :
  (I : Set)
  (D : Desc I)
  (P : (i : I) → μ I D i → Set)
  (pcon : (i : I) (xs : El I D (μ I D) i) → All I D (μ I D) P i xs → P i (con xs))
  (i : I)
  (x : μ I D i)
  → P i x

hyps :
  (I : Set)
  (D₁ : Desc I)
  (P : (i : I) → μ I D₁ i → Set)
  (pcon : (i : I) (xs : El I D₁ (μ I D₁) i) → All I D₁ (μ I D₁) P i xs → P i (con xs))
  (D₂ : Desc I)
  (i : I)
  (xs : El I D₂ (μ I D₁) i)
  → All I D₂ (μ I D₁) P i xs

ind I D P pcon i (con xs) = pcon i xs (hyps I D P pcon D i xs)

hyps I D P pcon (`Rec j A) i (x , xs) = ind I D P pcon j x , hyps I D P pcon A i xs
hyps I D P pcon (`End j) i q = tt
hyps I D P pcon (`Σ A B) i (a , b) = hyps I D P pcon (B a) i b
hyps I D P pcon (`Π A B) i f = λ a → hyps I D P pcon (B a) i (f a)

----------------------------------------------------------------------

data ℕT : Set where `zero `suc : ℕT
data VecT : Set where `nil `cons : VecT

ℕD : Desc ⊤
ℕD = `Σ ℕT λ
  { `zero → `End tt
  ; `suc → `Rec tt (`End tt)
  }

ℕ : ⊤ → Set
ℕ = μ ⊤ ℕD

zero : ℕ tt
zero = con (`zero , refl)

suc : ℕ tt → ℕ tt
suc n = con (`suc , n , refl)

VecD : (A : Set) → Desc (ℕ tt)
VecD A = `Σ VecT λ
  { `nil  → `End zero
  ; `cons → `Σ (ℕ tt) λ n → `Σ A λ _ → `Rec n (`End (suc n))
  }

Vec : (A : Set) (n : ℕ tt) → Set
Vec A n = μ (ℕ tt) (VecD A) n

nil : (A : Set) → Vec A zero
nil A = con (`nil , refl)

cons : (A : Set) (n : ℕ tt) (x : A) (xs : Vec A n) → Vec A (suc n)
cons A n x xs = con (`cons , n , x , xs , refl)

----------------------------------------------------------------------

addC : (u : ⊤) (xs : El ⊤ ℕD ℕ u)
  (ih : All ⊤ ℕD ℕ (λ u n → ℕ u → ℕ u) u xs)
  → ℕ u → ℕ u
addC tt (`zero , q) tt n = n
addC tt (`suc , m , q) (ih , tt) n = suc (ih n)

add : ℕ tt → ℕ tt → ℕ tt
add = ind ⊤ ℕD (λ _ _ → ℕ tt → ℕ tt) addC tt

multC : (u : ⊤) (xs : El ⊤ ℕD ℕ u)
  (ih : All ⊤ ℕD ℕ (λ u n → ℕ u → ℕ u) u xs)
  → ℕ u → ℕ u
multC tt (`zero , q) tt n = zero
multC tt (`suc , m , q) (ih , tt) n = add n (ih n)

mult : ℕ tt → ℕ tt → ℕ tt
mult = ind ⊤ ℕD (λ _ _ → ℕ tt → ℕ tt) multC tt

appendC : (u : ⊤) (A : Set) (m : ℕ u) (xs : El (ℕ u) (VecD A) (Vec A) m)
  (ih : All (ℕ u) (VecD A) (Vec A) (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)) m xs)
  (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)
appendC tt A .(con (`zero , refl)) (`nil , refl) ih n ys = ys
appendC tt A .(con (`suc , m , refl)) (`cons , m , x , xs , refl) (ih , tt) n ys = cons A (add m n) x (ih n ys)

append : (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n) 
append A = ind (ℕ tt) (VecD A) (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)) (appendC tt A)

concatC : (u : ⊤) (A : Set) (m n : ℕ u) (xss : El (ℕ u) (VecD (Vec A m)) (Vec (Vec A m)) n)
  (ih : All (ℕ u) (VecD (Vec A m)) (Vec (Vec A m)) (λ n xss → Vec A (mult n m)) n xss)
  → Vec A (mult n m)
concatC tt A m .(con (`zero , refl)) (`nil , refl) tt = nil A
concatC tt A m .(con (`suc , n , refl)) (`cons , n , xs , xss , refl) (ih , tt) = append A m xs (mult n m) ih

concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Vec A (mult n m)
concat A m = ind (ℕ tt) (VecD (Vec A m)) (λ n xss → Vec A (mult n m)) (concatC tt A m)

-------------------------------------------------------------------------------
