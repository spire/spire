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

data Elem {A : Set} : List A → Set where
  here : ∀{x xs} → Elem (x ∷ xs)
  there : ∀{x xs} → Elem xs → Elem (x ∷ xs)

elimElem : {A : Set} (P : (xs : List A) → Elem xs → Set)
  (phere : (x : A) (xs : List A) → P (x ∷ xs) here)
  (pthere : (x : A) (xs : List A) (t : Elem xs) → P xs t → P (x ∷ xs) (there t))
  (xs : List A) (t : Elem xs) → P xs t
elimElem P phere pthere (x ∷ xs) here = phere x xs
elimElem P phere pthere (x ∷ xs) (there t) = pthere x xs t (elimElem P phere pthere xs t)

----------------------------------------------------------------------

data Tel : Set₁ where
  End : Tel
  Arg : (A : Set) (B : A → Tel) → Tel

elimTel : (P : Tel → Set)
  (pend : P End)
  (parg  : (A : Set) (B : A → Tel) (pb : (a : A) → P (B a)) → P (Arg A B))
  (T : Tel) → P T
elimTel P pend parg End = pend
elimTel P pend parg (Arg A B) = parg A B (λ a → elimTel P pend parg (B a))

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

Elᴰ : {I : Set} (D : Desc I) → (I → Set) → I → Set
Elᴰ (End j) X i = j ≡ i
Elᴰ (Rec j D)  X i = Σ (X j) (λ _ → Elᴰ D X i)
Elᴰ (Arg A B)  X i = Σ A (λ a → Elᴰ (B a) X i)

Hyps : {I : Set} (D : Desc I) (X : I → Set) (P : (i : I) → X i → Set) (i : I) (xs : Elᴰ D X i) → Set
Hyps (End j) X P i q = ⊤
Hyps (Rec j D)  X P i (x , xs) = Σ (P j x) (λ _ → Hyps D X P i xs)
Hyps (Arg A B)  X P i (a , b) = Hyps (B a) X P i b

----------------------------------------------------------------------

data μ (ℓ : String) (P : Set) (I : P → Set) (p : P) (D : Desc (I p)) (i : I p) : Set where
  init : Elᴰ D (μ ℓ P I p D) i → μ ℓ P I p D i

ind : {ℓ : String} {P : Set} {I : P → Set} {p : P} (D : Desc (I p))
  (M : (i : I p) → μ ℓ P I p D i → Set)
  (α : ∀ i (xs : Elᴰ D (μ ℓ P I p D) i) (ihs : Hyps D (μ ℓ P I p D) M i xs) → M i (init xs))
  (i : I p)
  (x : μ ℓ P I p D i)
  → M i x

prove : {ℓ : String} {P : Set} {I : P → Set} {p : P} (D E : Desc (I p))
  (M : (i : I p) → μ ℓ P I p E i → Set)
  (α : ∀ i (xs : Elᴰ E (μ ℓ P I p E) i) (ihs : Hyps E (μ ℓ P I p E) M i xs) → M i (init xs))
  (i : (I p)) (xs : Elᴰ D (μ ℓ P I p E) i) → Hyps D (μ ℓ P I p E) M i xs

ind D M α i (init xs) = α i xs (prove D D M α i xs)

prove (End j) E M α i q = tt
prove (Rec j D) E M α i (x , xs) = ind E M α j x , prove D E M α i xs
prove (Arg A B) E M α i (a , xs) = prove (B a) E M α i xs

----------------------------------------------------------------------
