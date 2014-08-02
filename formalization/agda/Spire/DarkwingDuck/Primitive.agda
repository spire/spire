{-# OPTIONS --type-in-type --no-positivity-check #-}
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

elimPair : {A : Set} {B : A → Set}
  (P : Σ A B → Set)
  (ppair : (a : A) (b : B a) → P (a , b))
  (ab : Σ A B) → P ab
elimPair P ppair (a , b) = ppair a b

----------------------------------------------------------------------

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

elimEq : {A : Set} {x : A} (P : (y : A) → x ≡ y → Set)
  (prefl : P x refl)
  (y : A) (q : x ≡ y) → P y q
elimEq P prefl x refl = prefl

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

FuncM : (I : Set) → Desc I → Set
FuncM I D = (I → Set) → I → Set

Func : (I : Set) (D : Desc I) → FuncM I D
Func I = elimDesc I (FuncM I)
  (λ j X i → j ≡ i)
  (λ j D ih X i → Σ (X j) (λ _ → ih X i))
  (λ A B ih X i → Σ A (λ a → ih a X i))

HypsM : (I : Set) → Desc I → Set
HypsM I D = (X : I → Set) (P : (i : I) → X i → Set) (i : I) (xs : Func I D X i) → Set

Hyps : (I : Set) (D : Desc I) → HypsM I D
Hyps I = elimDesc I (HypsM I)
  (λ j X P i q → ⊤)
  (λ j D ih X P i → elimPair (λ _ → Set) (λ x xs → Σ (P j x) (λ _ → ih X P i xs)))
  (λ A B ih X P i → elimPair (λ _ → Set) (λ a xs → ih a X P i xs))

----------------------------------------------------------------------

data μ (ℓ : String) (P I : Set) (D : Desc I) (p : P) (i : I) : Set where
  init : Func I D (μ ℓ P I D p) i → μ ℓ P I D p i

All : (I : Set) → Desc I → Set
All I D = (X : I → Set) (P : (i : I) → X i → Set)
  (p : (i : I) (x : X i) → P i x)
  (i : I) (xs : Func I D X i)
  → Hyps I D X P i xs

all : (I : Set) (D : Desc I) → All I D
all I = elimDesc I (All I)
  (λ j X P p i q → tt)
  (λ j D ih X P p i → elimPair (λ ab → Hyps I (Rec j D) X P i ab)
    (λ x xs → p j x , ih X P p i xs))
  (λ A B ih X P p i → elimPair (λ ab → Hyps I (Arg A B) X P i ab)
    (λ a xs → ih a X P p i xs))

{-# NO_TERMINATION_CHECK #-}
ind : (ℓ : String) (P I : Set) (D : Desc I) (p : P)
  (M : (i : I) → μ ℓ P I D p i → Set)
  (α : ∀ i (xs : Func I D (μ ℓ P I D p) i) (ihs : Hyps I D (μ ℓ P I D p) M i xs) → M i (init xs))
  (i : I)
  (x : μ ℓ P I D p i)
  → M i x
ind ℓ P I D p M α i (init xs) = α i xs (all I D (μ ℓ P I D p) M (ind ℓ P I D p M α) i xs)

----------------------------------------------------------------------
