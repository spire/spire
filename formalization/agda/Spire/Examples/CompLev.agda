{-# OPTIONS --type-in-type #-}
open import Data.Unit
open import Data.Product hiding ( curry ; uncurry )
open import Data.List hiding ( concat )
open import Data.String
open import Relation.Binary.PropositionalEquality
open import Function
module Spire.Examples.CompLev where

----------------------------------------------------------------------

Label : Set
Label = String

Enum : Set
Enum = List Label

data Tag : Enum → Set where
  here : ∀{l E} → Tag (l ∷ E)
  there : ∀{l E} → Tag E → Tag (l ∷ E)

Branches : (E : Enum) (P : Tag E → Set) → Set
Branches [] P = ⊤
Branches (l ∷ E) P = P here × Branches E (λ t → P (there t))

case : {E : Enum} (P : Tag E → Set) (cs : Branches E P) (t : Tag E) → P t
case P (c , cs) here = c
case P (c , cs) (there t) = case (λ t → P (there t)) cs t

----------------------------------------------------------------------

data Tel : Set where
  End : Tel
  Arg : (A : Set) (B : A → Tel) → Tel

Elᵀ  : Tel → Set
Elᵀ End = ⊤
Elᵀ (Arg A B) = Σ A (λ a → Elᵀ (B a))

----------------------------------------------------------------------

data Desc (I : Set) : Set where
  End : Desc I
  Rec : (i : I) (D : Desc I) → Desc I
  RecFun : (A : Set) (B : A → I) (D : Desc I) → Desc I
  Arg : (A : Set) (B : A → Desc I) → Desc I

----------------------------------------------------------------------

ISet : Set → Set
ISet I = I → Set

Elᴰ : {I : Set} (D : Desc I) → ISet I → Set
Elᴰ End X = ⊤
Elᴰ (Rec j D) X = X j × Elᴰ D X
Elᴰ (RecFun A B D) X = ((a : A) → X (B a)) × Elᴰ D X
Elᴰ (Arg A B) X = Σ A (λ a → Elᴰ (B a) X)

Hyps : {I : Set} (D : Desc I) (X : ISet I) (P : (i : I) → X i → Set) (xs : Elᴰ D X) → Set
Hyps End X P tt = ⊤
Hyps (Rec i D) X P (x , xs) = P i x × Hyps D X P xs
Hyps (RecFun A B D) X P (f , xs) = ((a : A) → P (B a) (f a)) × Hyps D X P xs
Hyps (Arg A B) X P (a , xs) = Hyps (B a) X P xs

----------------------------------------------------------------------

data μ {I : Set} (R : I → Desc I) (i : I) : Set where
  init : Elᴰ (R i) (μ R) → μ R i

----------------------------------------------------------------------

ind : {I : Set} (R : I → Desc I)
  (M : (i : I) → μ R i → Set)
  (α : ∀ i (xs : Elᴰ (R i) (μ R)) (ihs : Hyps (R i) (μ R) M xs) → M i (init xs))
  (i : I)
  (x : μ R i)
  → M i x

prove : {I : Set} (D : Desc I) (R : I → Desc I)
  (M : (i : I) → μ R i → Set)
  (α : ∀ i (xs : Elᴰ (R i) (μ R)) (ihs : Hyps (R i) (μ R) M xs) → M i (init xs))
  (xs : Elᴰ D (μ R)) → Hyps D (μ R) M xs

ind R M α i (init xs) = α i xs (prove (R i) R M α xs)

prove End R M α tt = tt
prove (Rec j D) R M α (x , xs) = ind R M α j x , prove D R M α xs
prove (RecFun A B D) R M α (f , xs) = (λ a → ind R M α (B a) (f a)) , prove D R M α xs
prove (Arg A B) R M α (a , xs) = prove (B a) R M α xs

----------------------------------------------------------------------

DescE : Enum
DescE = "End" ∷ "Rec" ∷ "Arg" ∷ []

DescT : Set
DescT = Tag DescE

-- EndT : DescT
pattern EndT = here

-- RecT : DescT
pattern RecT = there here

-- ArgT : DescT
pattern ArgT = there (there here)

DescR : Set → ⊤ → Desc ⊤
DescR I tt = Arg (Tag DescE)
  (case (λ _ → Desc ⊤) (
      (Arg I λ i → End)
    , (Arg I λ i → Rec tt End)
    , (Arg Set λ A → RecFun A (λ a → tt) End)
    , tt
  ))

`Desc : (I : Set) → Set
`Desc I = μ (DescR I) tt

-- `End : {I : Set} (i : I) → `Desc I
pattern `End i = init (EndT , i , tt)

-- `Rec : {I : Set} (i : I) (D : `Desc I) → `Desc I
pattern `Rec i D = init (RecT , i , D , tt)

-- `Arg : {I : Set} (A : Set) (B : A → `Desc I) → `Desc I
pattern `Arg A B = init (ArgT , A , B , tt)

----------------------------------------------------------------------

FixI : (I : Set) → Set
FixI I = I × `Desc I

FixR' : (I : Set) (D : `Desc I) → I → `Desc I → Desc (FixI I)
FixR' I D i (`End j) = Arg (j ≡ i) λ q → End
FixR' I D i (`Rec j E) = Rec (j , D) (FixR' I D i E)
FixR' I D i (`Arg A B) = Arg A λ a → FixR' I D i (B a)
FixR' I D i (init (there (there (there ())) , xs))

FixR : (I : Set) (D : `Desc I) → FixI I → Desc (FixI I)
FixR I D E,i = FixR' I D (proj₁ E,i) (proj₂ E,i)

`Fix : (I : Set) (D : `Desc I) (i : I) → Set
`Fix I D i = μ (FixR I D) (i , D)

----------------------------------------------------------------------
