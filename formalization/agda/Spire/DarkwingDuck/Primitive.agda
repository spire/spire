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

elimElem : (A : Set) (P : (xs : List A) → Elem A xs → Set)
  (phere : (x : A) (xs : List A) → P (x ∷ xs) here)
  (pthere : (x : A) (xs : List A) (t : Elem A xs) → P xs t → P (x ∷ xs) (there t))
  (xs : List A) (t : Elem A xs) → P xs t
elimElem A P phere pthere (x ∷ xs) here = phere x xs
elimElem A P phere pthere (x ∷ xs) (there t) = pthere x xs t (elimElem A P phere pthere xs t)

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

elimDesc : {I : Set} (P : Desc I → Set)
  (pend : (i : I) → P (End i))
  (prec  : (i : I) (D : Desc I) (pd : P D) → P (Rec i D))
  (parg : (A : Set) (B : A → Desc I) (pb : (a : A) → P (B a)) → P (Arg A B))
  (D : Desc I) → P D
elimDesc P pend prec parg (End i) = pend i
elimDesc P pend prec parg (Rec i D) = prec i D (elimDesc P pend prec parg D)
elimDesc P pend prec parg (Arg A B) = parg A B (λ a → elimDesc P pend prec parg (B a))

Func : (I : Set) (D : Desc I) → (I → Set) → I → Set
Func I = elimDesc
  (λ D → (I → Set) → I → Set)
  (λ j X i → j ≡ i)
  (λ j D ih X i → Σ (X j) (λ _ → ih X i))
  (λ A B ih X i → Σ A (λ a → ih a X i))

Hyps : (I : Set) (D : Desc I) (X : I → Set) (P : (i : I) → X i → Set) (i : I) (xs : Func I D X i) → Set
Hyps I = elimDesc
  (λ D → (X : I → Set) (P : (i : I) → X i → Set) (i : I) (xs : Func I D X i) → Set)
  (λ j X P i q → ⊤)
  (λ j D ih X P i x,xs → elimPair (λ ab → Set) (λ x xs → Σ (P j x) (λ _ → ih X P i xs)) x,xs)
  (λ A B ih X P i a,xs → elimPair (λ ab → Set) (λ a xs → ih a X P i xs) a,xs)

----------------------------------------------------------------------

data μ (ℓ : String) (P : Set) (I : P → Set) (p : P) (D : Desc (I p)) (i : I p) : Set where
  init : Func (I p) D (μ ℓ P I p D) i → μ ℓ P I p D i

all : {I : Set} (D : Desc I) (X : I → Set) (P : (i : I) → X i → Set)
  (p : (i : I) (x : X i) → P i x) (i : I) (xs : Func I D X i)
  → Hyps I D X P i xs
all (End j) X P p i q = tt
all (Rec j D) X P p i (x , xs) = p j x , all D X P p i xs
all (Arg A B) X P p i (a , xs) = all (B a) X P p i xs

{-# NO_TERMINATION_CHECK #-}
ind : (ℓ : String) (P : Set) (I : P → Set) (p : P) (D : Desc (I p))
  (M : (i : I p) → μ ℓ P I p D i → Set)
  (α : ∀ i (xs : Func (I p) D (μ ℓ P I p D) i) (ihs : Hyps (I p) D (μ ℓ P I p D) M i xs) → M i (init xs))
  (i : I p)
  (x : μ ℓ P I p D i)
  → M i x
ind ℓ P I p D M α i (init xs) = α i xs (all D (μ ℓ P I p D) M (ind ℓ P I p D M α) i xs)

----------------------------------------------------------------------
