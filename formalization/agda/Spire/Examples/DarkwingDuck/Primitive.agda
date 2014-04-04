module Spire.Examples.DarkwingDuck.Primitive where

----------------------------------------------------------------------

infixr 4 _,_
infixr 5 _∷_

postulate String : Set
{-# BUILTIN STRING String #-}

data ⊤ : Set where
  tt : ⊤

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (a : A) (b : B a) → Σ A B

_×_ : (A B : Set) → Set
A × B = Σ A (λ _ → B)

proj₁ : ∀{A B} → Σ A B → A
proj₁ (a , b) = a

proj₂ : ∀{A B} (ab : Σ A B) → B (proj₁ ab)
proj₂ (a , b) = b

data List (A : Set) : Set where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

----------------------------------------------------------------------

data Tag : List String → Set where
  here : ∀{l E} → Tag (l ∷ E)
  there : ∀{l E} → Tag E → Tag (l ∷ E)

Branches : (E : List String) (P : Tag E → Set) → Set
Branches [] P = ⊤
Branches (l ∷ E) P = P here × Branches E (λ t → P (there t))

case : {E : List String} (P : Tag E → Set) (cs : Branches E P) (t : Tag E) → P t
case P (c , cs) here = c
case P (c , cs) (there t) = case (λ t → P (there t)) cs t

----------------------------------------------------------------------

data Tel : Set₁ where
  End : Tel
  Arg : (A : Set) (B : A → Tel) → Tel

Elᵀ  : Tel → Set
Elᵀ End = ⊤
Elᵀ (Arg A B) = Σ A (λ a → Elᵀ (B a))

----------------------------------------------------------------------

data Desc (I : Set) : Set₁ where
  End : (i : I) → Desc I
  Rec : (i : I) (D : Desc I) → Desc I
  Arg : (A : Set) (B : A → Desc I) → Desc I

----------------------------------------------------------------------

Elᴰ : {I : Set} (D : Desc I) → (I → Set) → I → Set
Elᴰ (End j) X i = j ≡ i
Elᴰ (Rec j D) X i = X j × Elᴰ D X i
Elᴰ (Arg A B) X i = Σ A (λ a → Elᴰ (B a) X i)

Hyps : {I : Set} (D : Desc I) (X : I → Set) (P : (i : I) → X i → Set) (i : I) (xs : Elᴰ D X i) → Set
Hyps (End j) X P i q = ⊤
Hyps (Rec j D) X P i (x , xs) = P j x × Hyps D X P i xs
Hyps (Arg A B) X P i (a , b) = Hyps (B a) X P i b

----------------------------------------------------------------------

data μ {I : Set} (D : Desc I) (i : I) : Set where
  init : Elᴰ D (μ D) i → μ D i

----------------------------------------------------------------------

ind : {I : Set} (D : Desc I)
  (M : (i : I) → μ D i → Set)
  (α : ∀ i (xs : Elᴰ D (μ D) i) (ihs : Hyps D (μ D) M i xs) → M i (init xs))
  (i : I)
  (x : μ D i)
  → M i x

prove : {I : Set} (D E : Desc I)
  (M : (i : I) → μ E i → Set)
  (α : ∀ i (xs : Elᴰ E (μ E) i) (ihs : Hyps E (μ E) M i xs) → M i (init xs))
  (i : I) (xs : Elᴰ D (μ E) i) → Hyps D (μ E) M i xs

ind D M α i (init xs) = α i xs (prove D D M α i xs)

prove (End j) E M α i q = tt
prove (Rec j D) E M α i (x , xs) = ind E M α j x , prove D E M α i xs
prove (Arg A B) E M α i (a , xs) = prove (B a) E M α i xs

----------------------------------------------------------------------
