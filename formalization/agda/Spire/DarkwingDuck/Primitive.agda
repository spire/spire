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

data PointsTo (A : Set) : List A → Set where
  here : ∀{x xs} → PointsTo A (x ∷ xs)
  there : ∀{x xs} → PointsTo A xs → PointsTo A (x ∷ xs)

elimPointsTo : {A : Set} (P : (xs : List A) → PointsTo A xs → Set)
  (phere : (x : A) (xs : List A) → P (x ∷ xs) here)
  (pthere : (x : A) (xs : List A) (t : PointsTo A xs) → P xs t → P (x ∷ xs) (there t))
  (xs : List A) (t : PointsTo A xs) → P xs t
elimPointsTo P phere pthere (x ∷ xs) here = phere x xs
elimPointsTo P phere pthere (x ∷ xs) (there t) = pthere x xs t (elimPointsTo P phere pthere xs t)

----------------------------------------------------------------------

data Tel : Set₁ where
  End : Tel
  Arg IArg : (A : Set) (B : A → Tel) → Tel

elimTel : (P : Tel → Set)
  (pend : P End)
  (parg  : (A : Set) (B : A → Tel) (pb : (a : A) → P (B a)) → P (Arg A B))
  (piarg : (A : Set) (B : A → Tel) (pb : (a : A) → P (B a)) → P (IArg A B))
  (T : Tel) → P T
elimTel P pend parg piarg End = pend
elimTel P pend parg piarg (Arg A B) = parg A B (λ a → elimTel P pend parg piarg (B a))
elimTel P pend parg piarg (IArg A B) = piarg A B (λ a → elimTel P pend parg piarg (B a))

----------------------------------------------------------------------

data Desc (I : Set) : Set₁ where
  End : (i : I) → Desc I
  Rec : (i : I) (D : Desc I) → Desc I
  Arg : (A : Set) (B : A → Desc I) → Desc I
  IArg : (A : Set) (B : A → Desc I) → Desc I

elimDesc : {I : Set} (P : Desc I → Set)
  (pend : (i : I) → P (End i))
  (prec  : (i : I) (D : Desc I) (pd : P D) → P (Rec i D))
  (parg : (A : Set) (B : A → Desc I) (pb : (a : A) → P (B a)) → P (Arg A B))
  (piarg : (A : Set) (B : A → Desc I) (pb : (a : A) → P (B a)) → P (IArg A B))
  (D : Desc I) → P D
elimDesc P pend prec parg piarg (End i) = pend i
elimDesc P pend prec parg piarg (Rec i D) = prec i D (elimDesc P pend prec parg piarg D)
elimDesc P pend prec parg piarg (Arg A B) = parg A B (λ a → elimDesc P pend prec parg piarg (B a))
elimDesc P pend prec parg piarg (IArg A B) = piarg A B (λ a → elimDesc P pend prec parg piarg (B a))

Elᴰ : {I : Set} (D : Desc I) → (I → Set) → I → Set
Elᴰ (End j) X i = j ≡ i
Elᴰ (Rec j D)  X i = Σ (X j) (λ _ → Elᴰ D X i)
Elᴰ (Arg A B)  X i = Σ A (λ a → Elᴰ (B a) X i)
Elᴰ (IArg A B) X i = Σ A (λ a → Elᴰ (B a) X i)

Hyps : {I : Set} (D : Desc I) (X : I → Set) (P : (i : I) → X i → Set) (i : I) (xs : Elᴰ D X i) → Set
Hyps (End j) X P i q = ⊤
Hyps (Rec j D)  X P i (x , xs) = Σ (P j x) (λ _ → Hyps D X P i xs)
Hyps (Arg A B)  X P i (a , b) = Hyps (B a) X P i b
Hyps (IArg A B) X P i (a , b) = Hyps (B a) X P i b

----------------------------------------------------------------------

data μ {I : Set} (D : Desc I) (i : I) : Set where
  init : Elᴰ D (μ D) i → μ D i

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
prove (Rec j D)  E M α i (x , xs) = ind E M α j x , prove D E M α i xs
prove (Arg A B)  E M α i (a , xs) = prove (B a) E M α i xs
prove (IArg A B) E M α i (a , xs) = prove (B a) E M α i xs

----------------------------------------------------------------------
