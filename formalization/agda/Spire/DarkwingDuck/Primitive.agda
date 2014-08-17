{-# OPTIONS --type-in-type #-}
module Spire.DarkwingDuck.Primitive where

----------------------------------------------------------------------

infixr 4 _,_
infixr 5 _∷_

----------------------------------------------------------------------

postulate String : Set
{-# BUILTIN STRING String #-}

----------------------------------------------------------------------

data ⊥ : Set where

elimBot : (P : ⊥ → Set)
  (v : ⊥) → P v
elimBot P ()

----------------------------------------------------------------------

data ⊤ : Set where
  tt : ⊤

elimUnit : (P : ⊤ → Set)
  (ptt : P tt)
  (u : ⊤) → P u
elimUnit P ptt tt = ptt

----------------------------------------------------------------------

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (a : A) (b : B a) → Σ A B

elimPair : (A : Set) (B : A → Set)
  (P : Σ A B → Set)
  (ppair : (a : A) (b : B a) → P (a , b))
  (ab : Σ A B) → P ab
elimPair A B P ppair (a , b) = ppair a b

----------------------------------------------------------------------

data _≡_ {A : Set} (x : A) : {B : Set} → B → Set where
  refl : x ≡ x

elimEq : (A : Set) (x : A) (P : (y : A) → x ≡ y → Set)
  (prefl : P x refl)
  (y : A) (q : x ≡ y) → P y q
elimEq A .x P prefl x refl = prefl

----------------------------------------------------------------------

data Enum : Set where
  []  : Enum
  _∷_ : (x : String) (xs : Enum) → Enum

elimEnum : (P : Enum → Set)
  (pnil : P [])
  (pcons : (x : String) (xs : Enum) → P xs → P (x ∷ xs))
  (xs : Enum) → P xs
elimEnum P pnil pcons [] = pnil
elimEnum P pnil pcons (x ∷ xs) = pcons x xs (elimEnum P pnil pcons xs)

----------------------------------------------------------------------

data Tag : Enum → Set where
  here : ∀{x xs} → Tag (x ∷ xs)
  there : ∀{x xs} → Tag xs → Tag (x ∷ xs)

Branches : (E : Enum) (P : Tag E → Set) → Set
Branches [] P = ⊤
Branches (l ∷ E) P = Σ (P here) (λ _ → Branches E (λ t → P (there t)))

case : (E : Enum) (P : Tag E → Set) (cs : Branches E P) (t : Tag E) → P t
case (ℓ ∷ E) P (c , cs) here = c
case (ℓ ∷ E) P (c , cs) (there t) = case E (λ t → P (there t)) cs t

----------------------------------------------------------------------

data Tel : Set₁ where
  Emp : Tel
  Ext : (A : Set) (B : A → Tel) → Tel

elimTel : (P : Tel → Set)
  (pemp : P Emp)
  (pext  : (A : Set) (B : A → Tel) (pb : (a : A) → P (B a)) → P (Ext A B))
  (T : Tel) → P T
elimTel P pemp pext Emp = pemp
elimTel P pemp pext (Ext A B) = pext A B (λ a → elimTel P pemp pext (B a))

----------------------------------------------------------------------

data Desc (I : Set) : Set₁ where
  End : (i : I) → Desc I
  Rec : (i : I) (D : Desc I) → Desc I
  Arg : (A : Set) (B : A → Desc I) → Desc I

elimDesc : (I : Set) (P : Desc I → Set)
  (pend : (i : I) → P (End i))
  (prec  : (i : I) (D : Desc I) (pd : P D) → P (Rec i D))
  (parg : (A : Set) (B : A → Desc I) (pb : (a : A) → P (B a)) → P (Arg A B))
  (D : Desc I) → P D
elimDesc I P pend prec parg (End i) = pend i
elimDesc I P pend prec parg (Rec i D) = prec i D (elimDesc I P pend prec parg D)
elimDesc I P pend prec parg (Arg A B) = parg A B (λ a → elimDesc I P pend prec parg (B a))

Func : (I : Set) (D : Desc I) → (I → Set) → I → Set
Func I (End j) X i = j ≡ i
Func I (Rec j D) X i = Σ (X j) (λ _ → Func I D X i)
Func I (Arg A B) X i = Σ A (λ a → Func I (B a) X i)

Hyps : (I : Set) (D : Desc I) (X : I → Set) (M : (i : I) → X i → Set) (i : I) (xs : Func I D X i) → Set
Hyps I (End j) X M i q = ⊤
Hyps I (Rec j D) X M i = elimPair (X j) (λ _ → Func I D X i) (λ _ → Set)
  (λ x xs → Σ (M j x) (λ _ → Hyps I D X M i xs))
Hyps I (Arg A B) X M i = elimPair A (λ a → Func I (B a) X i) (λ _ → Set)
  (λ a xs → Hyps I (B a) X M i xs)

----------------------------------------------------------------------

data μ (ℓ : String) (P I : Set) (D : Desc I) (p : P) (i : I) : Set where
  init : Func I D (μ ℓ P I D p) i → μ ℓ P I D p i

prove : (I : Set) (D : Desc I) (X : I → Set) (M : (i : I) → X i → Set)
  (m : (i : I) (x : X i) → M i x)
  (i : I) (xs : Func I D X i)
  → Hyps I D X M i xs
prove I (End j) X M m i q = tt
prove I (Rec j D) X M m i (x , xs) = m j x , prove I D X M m i xs
prove I (Arg A B) X M m i (a , xs) = prove I (B a) X M m i xs

{-# NO_TERMINATION_CHECK #-}
ind : (ℓ : String) (P I : Set) (D : Desc I) (p : P)
  (M : (i : I) → μ ℓ P I D p i → Set)
  (α : ∀ i (xs : Func I D (μ ℓ P I D p) i) (ihs : Hyps I D (μ ℓ P I D p) M i xs) → M i (init xs))
  (i : I)
  (x : μ ℓ P I D p i)
  → M i x
ind ℓ P I D p M α i (init xs) = α i xs (prove I D (μ ℓ P I D p) M (ind ℓ P I D p M α) i xs)

----------------------------------------------------------------------
