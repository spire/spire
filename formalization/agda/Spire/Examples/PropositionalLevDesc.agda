{-# OPTIONS --type-in-type #-}
open import Data.Unit
open import Data.Product hiding ( curry ; uncurry )
open import Data.List hiding ( concat )
open import Data.String
open import Relation.Binary.PropositionalEquality
module Spire.Examples.PropositionalLevDesc where

----------------------------------------------------------------------

Label : Set
Label = String

Enum : Set
Enum = List Label

data Tag : Enum → Set where
  here : ∀{l E} → Tag (l ∷ E)
  there : ∀{l E} → Tag E → Tag (l ∷ E)

Cases : (E : Enum) (P : Tag E → Set) → Set
Cases [] P = ⊤
Cases (l ∷ E) P = P here × Cases E λ t → P (there t)

case : (E : Enum) (P : Tag E → Set) (cs : Cases E P) (t : Tag E) → P t
case (l ∷ E) P (c , cs) here = c
case (l ∷ E) P (c , cs) (there t) = case E (λ t → P (there t)) cs t

UncurriedCases : (E : Enum) (P : Tag E → Set) (X : Set)
  → Set
UncurriedCases E P X = Cases E P → X

CurriedCases : (E : Enum) (P : Tag E → Set) (X : Set)
  → Set
CurriedCases [] P X = X
CurriedCases (l ∷ E) P X = P here → CurriedCases E (λ t → P (there t)) X

curryCases : (E : Enum) (P : Tag E → Set) (X : Set)
  (f : UncurriedCases E P X) → CurriedCases E P X
curryCases [] P X f = f tt
curryCases (l ∷ E) P X f = λ c → curryCases E (λ t → P (there t)) X (λ cs → f (c , cs))

uncurryCases : (E : Enum) (P : Tag E → Set) (X : Set)
  (f : CurriedCases E P X) → UncurriedCases E P X
uncurryCases [] P X x tt = x
uncurryCases (l ∷ E) P X f (c , cs) = uncurryCases E (λ t → P (there t)) X (f c) cs

----------------------------------------------------------------------

data Desc (I : Set) : Set₁ where
  `End : (i : I) → Desc I
  `Rec : (i : I) (D : Desc I) → Desc I
  `Arg : (A : Set) (B : A → Desc I) → Desc I
  `RecFun : (A : Set) (B : A → I) (D : Desc I) → Desc I

ISet : Set → Set₁
ISet I = I → Set

El : (I : Set) (D : Desc I) (X : ISet I) → ISet I
El I (`End j) X i = j ≡ i
El I (`Rec j D) X i = X j × El I D X i
El I (`Arg A B) X i = Σ A (λ a → El I (B a) X i)
El I (`RecFun A B D) X i = ((a : A) → X (B a)) × El I D X i

Hyps : (I : Set) (D : Desc I) (X : ISet I) (P : (i : I) → X i → Set) (i : I) (xs : El I D X i) → Set
Hyps I (`End j) X P i q = ⊤
Hyps I (`Rec j D) X P i (x , xs) = P j x × Hyps I D X P i xs
Hyps I (`Arg A B) X P i (a , b) = Hyps I (B a) X P i b
Hyps I (`RecFun A B D) X P i (f , xs) = ((a : A) → P (B a) (f a)) × Hyps I D X P i xs

----------------------------------------------------------------------

TagDesc : (I : Set) → Set
TagDesc I = Σ Enum (λ E → Cases E (λ _ → Desc I))

toCase : (I : Set) (E,cs : TagDesc I) → Tag (proj₁ E,cs) → Desc I
toCase I (E , cs) = case E (λ _ → Desc I) cs

toDesc : (I : Set) → TagDesc I → Desc I
toDesc I (E , cs) = `Arg (Tag E) (toCase I (E , cs))

----------------------------------------------------------------------

UncurriedEl : (I : Set) (D : Desc I) (X : ISet I) → Set
UncurriedEl I D X = {i : I} → El I D X i → X i

CurriedEl : (I : Set) (D : Desc I) (X : ISet I) → Set
CurriedEl I (`End i) X = X i
CurriedEl I (`Rec j D) X = (x : X j) → CurriedEl I D X
CurriedEl I (`Arg A B) X = (a : A) → CurriedEl I (B a) X
CurriedEl I (`RecFun A B D) X = ((a : A) → X (B a)) → CurriedEl I D X

curryEl : (I : Set) (D : Desc I) (X : ISet I)
  (cn : UncurriedEl I D X) → CurriedEl I D X
curryEl I (`End i) X cn = cn refl
curryEl I (`Rec i D) X cn = λ x → curryEl I D X (λ xs → cn (x , xs))
curryEl I (`Arg A B) X cn = λ a → curryEl I (B a) X (λ xs → cn (a , xs))
curryEl I (`RecFun A B D) X cn = λ f → curryEl I D X (λ xs → cn (f , xs))

uncurryEl : (I : Set) (D : Desc I) (X : ISet I)
  (cn : CurriedEl I D X) → UncurriedEl I D X
uncurryEl I (`End i) X cn refl = cn
uncurryEl I (`Rec i D) X cn (x , xs) = uncurryEl I D X (cn x) xs
uncurryEl I (`Arg A B) X cn (a , xs) = uncurryEl I (B a) X (cn a) xs
uncurryEl I (`RecFun A B D) X cn (f , xs) = uncurryEl I D X (cn f) xs

----------------------------------------------------------------------

CasesD : (I : Set) (E : Enum) → Set
CasesD I E = Cases E (λ _ → Desc I)

Args : (I : Set) (E : Enum) (t : Tag E) (cs : CasesD I E) → Desc I
Args I E t cs = case E (λ _ → Desc I) cs t

----------------------------------------------------------------------

data μ (I : Set) (E : Enum) (cs : CasesD I E) : I → Set where
  con : (t : Tag E) → UncurriedEl I (Args I E t cs) (μ I E cs)

con2 : (I : Set) (E : Enum) (cs : CasesD I E) (t : Tag E)
  → CurriedEl I (Args I E t cs) (μ I E cs)
con2 I E cs t = curryEl I (Args I E t cs) (μ I E cs) (con t)

----------------------------------------------------------------------

UncurriedHyps : (I : Set) (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : {i : I} → El I D X i → X i)
  → Set
UncurriedHyps I D X P cn =
  (i : I) (xs : El I D X i) → Hyps I D X P i xs → P i (cn xs)

CurriedHyps : (I : Set) (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedEl I D X)
  → Set
CurriedHyps I (`End i) X P cn =
  P i (cn refl)
CurriedHyps I (`Rec i D) X P cn =
  (x : X i) → P i x → CurriedHyps I D X P (λ xs → cn (x , xs))
CurriedHyps I (`Arg A B) X P cn =
  (a : A) → CurriedHyps I (B a) X P (λ xs → cn (a , xs))
CurriedHyps I (`RecFun A B D) X P cn =
  (f : (a : A) → X (B a)) (ihf : (a : A) → P (B a) (f a)) → CurriedHyps I D X P (λ xs → cn (f , xs))

curryHyps : (I : Set) (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedEl I D X)
  (pf : UncurriedHyps I D X P cn)
  → CurriedHyps I D X P cn
curryHyps I (`End i) X P cn pf =
  pf i refl tt
curryHyps I (`Rec i D) X P cn pf =
  λ x ih → curryHyps I D X P (λ xs → cn (x , xs)) (λ i xs ihs → pf i (x , xs) (ih , ihs))
curryHyps I (`Arg A B) X P cn pf =
  λ a → curryHyps I (B a) X P (λ xs → cn (a , xs)) (λ i xs ihs → pf i (a , xs) ihs)
curryHyps I (`RecFun A B D) X P cn pf =
  λ f ihf → curryHyps I D X P (λ xs → cn (f , xs)) (λ i xs ihs → pf i (f , xs) (ihf , ihs))

uncurryHyps : (I : Set) (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedEl I D X)
  (pf : CurriedHyps I D X P cn)
  → UncurriedHyps I D X P cn
uncurryHyps I (`End .i) X P cn pf i refl tt =
  pf
uncurryHyps I (`Rec j D) X P cn pf i (x , xs) (ih , ihs) =
  uncurryHyps I D X P (λ ys → cn (x , ys)) (pf x ih) i xs ihs
uncurryHyps I (`Arg A B) X P cn pf i (a , xs) ihs =
  uncurryHyps I (B a) X P (λ ys → cn (a , ys)) (pf a) i xs ihs
uncurryHyps I (`RecFun A B D) X P cn pf i (f , xs) (ihf , ihs) =
  uncurryHyps I D X P (λ ys → cn (f , ys)) (pf f ihf) i xs ihs

----------------------------------------------------------------------

ind :
  (I : Set)
  (E : Enum)
  (cs : CasesD I E)
  (P : (i : I) → μ I E cs i → Set)
  (pcon : (t : Tag E) → UncurriedHyps I (Args I E t cs) (μ I E cs) P (con t))
  (i : I)
  (x : μ I E cs i)
  → P i x

hyps :
  (I : Set)
  (E : Enum)
  (cs : CasesD I E)
  (P : (i : I) → μ I E cs i → Set)
  (pcon : (t : Tag E) → UncurriedHyps I (Args I E t cs) (μ I E cs) P (con t))
  (D : Desc I)
  (i : I)
  (xs : El I D (μ I E cs) i)
  → Hyps I D (μ I E cs) P i xs

ind I E cs P pcon i (con t as) = pcon t i as (hyps I E cs P pcon (Args I E t cs) i as)

hyps I E cs P pcon (`End j) i q = tt
hyps I E cs P pcon (`Rec j A) i (x , xs) = ind I E cs P pcon j x , hyps I E cs P pcon A i xs
hyps I E cs P pcon (`Arg A B) i (a , b) = hyps I E cs P pcon (B a) i b
hyps I E cs P pcon (`RecFun A B D) i (f , xs) = (λ a → ind I E cs P pcon (B a) (f a)) , hyps I E cs P pcon D i xs

----------------------------------------------------------------------

ind2 :
  (I : Set)
  (E : Enum)
  (cs : CasesD I E)
  (P : (i : I) → μ I E cs i → Set)
  (pcon : (t : Tag E) → CurriedHyps I (Args I E t cs) (μ I E cs) P (con t))
  (i : I)
  (x : μ I E cs i)
  → P i x
ind2 I E cs P pcon i x =
  ind I E cs P (λ t → uncurryHyps I (Args I E t cs) (μ I E cs) P (con t) (pcon t)) i x

elim :
  (I : Set)
  (E : Enum)
  (cs : CasesD I E)
  (P : (i : I) → μ I E cs i → Set)
  → let
    Q = λ t → CurriedHyps I (Args I E t cs) (μ I E cs) P (con t)
    X = (i : I) (x : μ I E cs i) → P i x
  in UncurriedCases E Q X
elim I E cs P ds i x =
  let Q = λ t → CurriedHyps I (Args I E t cs) (μ I E cs) P (con t)
  in ind2 I E cs P (case E Q ds) i x

elim2 :
  (I : Set)
  (E : Enum)
  (cs : CasesD I E)
  (P : (i : I) → μ I E cs i → Set)
  → let
    Q = λ t → CurriedHyps I (Args I E t cs) (μ I E cs) P (con t)
    X = (i : I) (x : μ I E cs i) → P i x
  in CurriedCases E Q X
elim2 I E cs P =
  let
    Q = λ t → CurriedHyps I (Args I E t cs) (μ I E cs) P (con t)
    X = (i : I) (x : μ I E cs i) → P i x
  in curryCases E Q X (elim I E cs P)

----------------------------------------------------------------------

ℕT : Enum
ℕT = "zero" ∷ "suc" ∷ []

VecT : Enum
VecT = "nil" ∷ "cons" ∷ []

ℕD : CasesD ⊤ ℕT
ℕD =
    `End tt
  , `Rec tt (`End tt)
  , tt

ℕ : ⊤ → Set
ℕ = μ ⊤ ℕT ℕD

zero : ℕ tt
zero = con here refl

suc : ℕ tt → ℕ tt
suc n = con (there here) (n , refl)

zero2 : ℕ tt
zero2 = con2 ⊤ ℕT ℕD here

suc2 : ℕ tt → ℕ tt
suc2 = con2 ⊤ ℕT ℕD (there here)

VecD : (A : Set) → CasesD (ℕ tt) VecT
VecD A =
    `End zero
  , `Arg (ℕ tt) (λ n → `Arg A λ _ → `Rec n (`End (suc n)))
  , tt

Vec : (A : Set) (n : ℕ tt) → Set
Vec A n = μ (ℕ tt) VecT (VecD A) n

nil : (A : Set) → Vec A zero
nil A = con here refl

cons : (A : Set) (n : ℕ tt) (x : A) (xs : Vec A n) → Vec A (suc n)
cons A n x xs = con (there here) (n , x , xs , refl)

nil2 : (A : Set) → Vec A zero
nil2 A = con2 (ℕ tt) VecT (VecD A) here

cons2 : (A : Set) (n : ℕ tt) (x : A) (xs : Vec A n) → Vec A (suc n)
cons2 A = con2 (ℕ tt) VecT (VecD A) (there here)

----------------------------------------------------------------------

module GenericEliminator where

  add : ℕ tt → ℕ tt → ℕ tt
  add = elim2 ⊤ ℕT ℕD _
    (λ n → n)
    (λ m ih n → suc (ih n))
    tt

  mult : ℕ tt → ℕ tt → ℕ tt
  mult = elim2 ⊤ ℕT ℕD _
    (λ n → zero)
    (λ m ih n → add n (ih n))
    tt

  append : (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)
  append A = elim2 (ℕ tt) VecT (VecD A) _
    (λ n ys → ys)
    (λ m x xs ih n ys → cons A (add m n) x (ih n ys))

  concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Vec A (mult n m)
  concat A m = elim2 (ℕ tt) VecT (VecD (Vec A m)) _
    (nil A)
    (λ n xs xss ih → append A m xs (mult n m) ih)

----------------------------------------------------------------------
