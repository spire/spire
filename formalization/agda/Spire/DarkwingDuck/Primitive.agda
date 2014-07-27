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

data List (A : Set) : Set where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

elimList : {A : Set} (P : List A → Set)
  (pnil : P [])
  (pcons : (x : A) (xs : List A) → P xs → P (x ∷ xs))
  (xs : List A) → P xs
elimList P pnil pcons [] = pnil
elimList P pnil pcons (x ∷ xs) = pcons x xs (elimList P pnil pcons xs)

----------------------------------------------------------------------

data Elem (A : Set) : List A → Set where
  here : ∀{x xs} → Elem A (x ∷ xs)
  there : ∀{x xs} → Elem A xs → Elem A (x ∷ xs)

elimElem : {A : Set} (P : (xs : List A) → Elem A xs → Set)
  (phere : (x : A) (xs : List A) → P (x ∷ xs) here)
  (pthere : (x : A) (xs : List A) (t : Elem A xs) → P xs t → P (x ∷ xs) (there t))
  (xs : List A) (t : Elem A xs) → P xs t
elimElem P phere pthere (x ∷ xs) here = phere x xs
elimElem P phere pthere (x ∷ xs) (there t) = pthere x xs t (elimElem P phere pthere xs t)

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
  Ref : (A : Set) (i : A → I) (D : Desc I) → Desc I
  Arg : (A : Set) (B : A → Desc I) → Desc I

elimDesc : {I : Set} (P : Desc I → Set)
  (pend : (i : I) → P (End i))
  (prec  : (i : I) (D : Desc I) (pd : P D) → P (Rec i D))
  (pref : (A : Set) (i : A → I) (D : Desc I) (pd : P D) → P (Ref A i D))
  (parg : (A : Set) (B : A → Desc I) (pb : (a : A) → P (B a)) → P (Arg A B))
  (D : Desc I) → P D
elimDesc P pend prec pref parg (End i) = pend i
elimDesc P pend prec pref parg (Rec i D) = prec i D (elimDesc P pend prec pref parg D)
elimDesc P pend prec pref parg (Ref A i D) = pref A i D (elimDesc P pend prec pref parg D)
elimDesc P pend prec pref parg (Arg A B) = parg A B (λ a → elimDesc P pend prec pref parg (B a))

FuncM : (I : Set) → Desc I → Set
FuncM I D = (I → Set) → I → Set

Func : (I : Set) (D : Desc I) → FuncM I D
Func I = elimDesc (FuncM I)
  (λ j X i → j ≡ i)
  (λ j D ih X i → Σ (X j) (λ _ → ih X i))
  (λ A j D ih X i → Σ ((a : A) → X (j a)) (λ _ → ih X i))
  (λ A B ih X i → Σ A (λ a → ih a X i))

HypsM : (I : Set) → Desc I → Set
HypsM I D = (X : I → Set) (P : (i : I) → X i → Set) (i : I) (xs : Func I D X i) → Set

Hyps : (I : Set) (D : Desc I) → HypsM I D
Hyps I = elimDesc (HypsM I)
  (λ j X P i q → ⊤)
  (λ j D ih X P i → elimPair (λ _ → Set) (λ x xs → Σ (P j x) (λ _ → ih X P i xs)))
  (λ A j D ih X P i → elimPair (λ _ → Set) (λ f xs → Σ ((a : A) → P (j a) (f a)) (λ _ → ih X P i xs)))
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
all I = elimDesc (All I)
  (λ j X P p i q → tt)
  (λ j D ih X P p i → elimPair (λ ab → Hyps I (Rec j D) X P i ab)
    (λ x xs → p j x , ih X P p i xs))
  (λ A j D ih X P p i → elimPair (λ ab → Hyps I (Ref A j D) X P i ab)
    (λ f xs → (λ a → p (j a) (f a)) , ih X P p i xs))
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
