{-# OPTIONS --type-in-type #-}
open import Data.Unit
open import Data.Product
open import Data.List hiding ( concat )
open import Data.String
open import Relation.Binary.PropositionalEquality
module Spire.Examples.LabelledDesc where

----------------------------------------------------------------------

Label : Set
Label = String

Enum : Set
Enum = List Label

data Tag : Enum → Set where
  here : ∀{l E} → Tag (l ∷ E)
  there : ∀{l E} → Tag E → Tag (l ∷ E)

data Cases2 (A : Set) : Enum → Set where -- Vec, Enum is ℕ, Tag is Fin
  [] : Cases2 A []
  _∷_ : ∀{l E} → A → Cases2 A E → Cases2 A (l ∷ E)

-- lookup
case2 : (E : Enum) (A : Set) → Cases2 A E → Tag E → A
case2 (l ∷ E) A (c ∷ cs) here = c
case2 (l ∷ E) A (c ∷ cs) (there t) = case2 E A cs t

Cases : (E : Enum) (P : Tag E → Set) → Set
Cases [] P = ⊤
Cases (l ∷ E) P = P here × Cases E λ t → P (there t)

case : (E : Enum) (P : Tag E → Set) (cs : Cases E P) (t : Tag E) → P t
case (l ∷ E) P (c , cs) here = c
case (l ∷ E) P (c , cs) (there t) = case E (λ t → P (there t)) cs t

----------------------------------------------------------------------

data Desc (I : Set) : Set₁ where
  `Rec : (i : I) (D : Desc I) → Desc I
  `End : (i : I) → Desc I
  `Σ `Π : (A : Set) (B : A → Desc I) → Desc I

ISet : Set → Set₁
ISet I = I → Set

El : (I : Set) (D : Desc I) (X : ISet I) → ISet I
El I (`End j)   X i = j ≡ i
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

caseD : (E : Enum) (I : Set) (cs : Cases E (λ _ → Desc I)) (t : Tag E) → Desc I
caseD E I cs t = case E (λ _ → Desc I) cs t

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

ℕT : Enum
ℕT = "zero" ∷ "suc" ∷ []

VecT : Enum
VecT = "nil" ∷ "cons" ∷ []

ℕC : Tag ℕT → Desc ⊤
ℕC = caseD ℕT ⊤
  ( `End tt
  , `Rec tt (`End tt)
  , tt
  )

ℕD : Desc ⊤
ℕD = `Σ (Tag ℕT) ℕC

ℕD2 : Desc ⊤
ℕD2 = `Σ (Tag ℕT) (case2 ℕT (Desc ⊤)
  ( `End tt
  ∷ `Rec tt (`End tt)
  ∷ []
  ))

ℕ : ⊤ → Set
ℕ = μ ⊤ ℕD

-- zero : ℕ tt
pattern zero = con (here , refl)

-- suc : ℕ tt → ℕ tt
pattern suc n = con (there here , n , refl)

VecC : (A : Set) → Tag VecT → Desc (ℕ tt)
VecC A = caseD VecT (ℕ tt)
  ( `End zero
  , `Σ (ℕ tt) (λ n → `Σ A λ _ → `Rec n (`End (suc n)))
  , tt
  )

VecD : (A : Set) → Desc (ℕ tt)
VecD A = `Σ (Tag VecT) (VecC A)

Vec : (A : Set) (n : ℕ tt) → Set
Vec A n = μ (ℕ tt) (VecD A) n

nil : (A : Set) → Vec A zero
nil A = con (here , refl)

cons : (A : Set) (n : ℕ tt) (x : A) (xs : Vec A n) → Vec A (suc n)
cons A n x xs = con (there here , n , x , xs , refl)

----------------------------------------------------------------------

add : ℕ tt → ℕ tt → ℕ tt
add = ind ⊤ ℕD (λ _ _ → ℕ tt → ℕ tt)
  (λ u xs → case ℕT
    (λ t → (c : El ⊤ (ℕC t) ℕ u)
           (ih : All ⊤ ℕD ℕ (λ u n → ℕ u → ℕ u) u (t , c))
           → ℕ u → ℕ u
    )
    ( (λ q ih n → n)
    , (λ m,q ih,tt n → suc (proj₁ ih,tt n))
    , tt
    )
    (proj₁ xs)
    (proj₂ xs)
  )
  tt

mult : ℕ tt → ℕ tt → ℕ tt
mult = ind ⊤ ℕD (λ _ _ → ℕ tt → ℕ tt)
  (λ u xs → case ℕT
    (λ t → (c : El ⊤ (ℕC t) ℕ u)
           (ih : All ⊤ ℕD ℕ (λ u n → ℕ u → ℕ u) u (t , c))
           → ℕ u → ℕ u
    )
    ( (λ q ih n → zero)
    , (λ m,q ih,tt n → add n (proj₁ ih,tt n))
    , tt
    )
    (proj₁ xs)
    (proj₂ xs)
  )
  tt

append : (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n) 
append A = ind (ℕ tt) (VecD A) (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n))
  (λ m xs → case VecT
    (λ t → (c : El (ℕ tt) (VecC A t) (Vec A) m)
           (ih : All (ℕ tt) (VecD A) (Vec A) (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)) m (t , c))
           (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)
    )
    ( (λ q ih n ys → subst (λ m → Vec A (add m n)) q ys)
    , (λ m',x,xs,q ih,tt n ys →
        let m' = proj₁ m',x,xs,q
            x = proj₁ (proj₂ m',x,xs,q)
            q = proj₂ (proj₂ (proj₂ m',x,xs,q))
            ih = proj₁ ih,tt
        in
        subst (λ m → Vec A (add m n)) q (cons A (add m' n) x (ih n ys))
      )
    , tt
    )
    (proj₁ xs)
    (proj₂ xs)
  )

concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Vec A (mult n m)
concat A m = ind (ℕ tt) (VecD (Vec A m)) (λ n xss → Vec A (mult n m))
  (λ n xss → case VecT
    (λ t → (c : El (ℕ tt) (VecC (Vec A m) t) (Vec (Vec A m)) n)
           (ih : All (ℕ tt) (VecD (Vec A m)) (Vec (Vec A m)) (λ n xss → Vec A (mult n m)) n (t , c))
           → Vec A (mult n m)
    )
    ( (λ q ih → subst (λ n → Vec A (mult n m)) q (nil A))
    , (λ n',xs,xss,q ih,tt →
        let n' = proj₁ n',xs,xss,q
            xs = proj₁ (proj₂ n',xs,xss,q)
            q = proj₂ (proj₂ (proj₂ n',xs,xss,q))
            ih = proj₁ ih,tt
        in
        subst (λ n → Vec A (mult n m)) q (append A m xs (mult n' m) ih)
      )
    , tt
    )
    (proj₁ xss)
    (proj₂ xss)
  )

-------------------------------------------------------------------------------
