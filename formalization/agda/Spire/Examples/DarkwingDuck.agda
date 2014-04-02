{-# OPTIONS --type-in-type #-}
open import Data.Unit
open import Data.Product hiding ( curry ; uncurry )
open import Data.List hiding ( concat )
open import Data.String
open import Relation.Binary.PropositionalEquality
open import Function
module Spire.Examples.DarkwingDuck where

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
  End : (i : I) → Desc I
  Rec : (i : I) (D : Desc I) → Desc I
  Arg : (A : Set) (B : A → Desc I) → Desc I

----------------------------------------------------------------------

ISet : Set → Set
ISet I = I → Set

Elᴰ : {I : Set} (D : Desc I) → ISet I → ISet I
Elᴰ (End j) X i = j ≡ i
Elᴰ (Rec j D) X i = X j × Elᴰ D X i
Elᴰ (Arg A B) X i = Σ A (λ a → Elᴰ (B a) X i)

----------------------------------------------------------------------

data μ {I : Set} (D : Desc I) (i : I) : Set where
  init : Elᴰ D (μ D) i → μ D i

----------------------------------------------------------------------

record Data : Set where
  field
    P : Tel
    I : Elᵀ P → Tel
    E : Enum
    B : (A : Elᵀ P) → Branches E (λ _ → Desc (Elᵀ (I A)))

  T : Set
  T = Tag E

  C : (A : Elᵀ P) → T → Desc (Elᵀ (I A))
  C A = case (λ _ → Desc (Elᵀ (I A))) (B A)

  D : (A : Elᵀ P) → Desc (Elᵀ (I A))
  D A = Arg T (C A)

----------------------------------------------------------------------

UncurriedBranches : (E : Enum) (P : Tag E → Set) (X : Set)
  → Set
UncurriedBranches E P X = Branches E P → X

CurriedBranches : (E : Enum) (P : Tag E → Set) (X : Set)
  → Set
CurriedBranches [] P X = X
CurriedBranches (l ∷ E) P X = P here → CurriedBranches E (λ t → P (there t)) X

curryBranches : {E : Enum} {P : Tag E → Set} {X : Set}
  → UncurriedBranches E P X → CurriedBranches E P X
curryBranches {[]} f = f tt
curryBranches {l ∷ E} f = λ c → curryBranches (λ cs → f (c , cs))

uncurryBranches : {E : Enum} {P : Tag E → Set} {X : Set}
  → CurriedBranches E P X → UncurriedBranches E P X
uncurryBranches {[]} x tt = x
uncurryBranches {l ∷ E} f (c , cs) = uncurryBranches (f c) cs

----------------------------------------------------------------------

UncurriedElᵀ : (T : Tel) (X : Elᵀ T → Set) → Set
UncurriedElᵀ T X = (xs : Elᵀ T) → X xs

CurriedElᵀ : (T : Tel) (X : Elᵀ T → Set) → Set
CurriedElᵀ End X = X tt
CurriedElᵀ (Arg A B) X = (a : A) → CurriedElᵀ (B a) (λ b → X (a , b))

curryElᵀ : (T : Tel) (X : Elᵀ T → Set)
  → UncurriedElᵀ T X → CurriedElᵀ T X
curryElᵀ End X f = f tt
curryElᵀ (Arg A B) X f = λ a → curryElᵀ (B a) (λ b → X (a , b)) (λ b → f (a , b))

ICurriedElᵀ : (T : Tel) (X : Elᵀ T → Set) → Set
ICurriedElᵀ End X = X tt
ICurriedElᵀ (Arg A B) X = {a : A} → ICurriedElᵀ (B a) (λ b → X (a , b))

icurryElᵀ : (T : Tel) (X : Elᵀ T → Set)
  → UncurriedElᵀ T X → ICurriedElᵀ T X
icurryElᵀ End X f = f tt
icurryElᵀ (Arg A B) X f = λ {a} → icurryElᵀ (B a) (λ b → X (a , b)) (λ b → f (a , b))

iuncurryElᵀ : (T : Tel) (X : Elᵀ T → Set)
  → ICurriedElᵀ T X → UncurriedElᵀ T X
iuncurryElᵀ End X x tt = x
iuncurryElᵀ (Arg A B) X f (a , b) = iuncurryElᵀ (B a) (λ b → X (a , b)) f b

----------------------------------------------------------------------

UncurriedElᴰ : {I : Set} (D : Desc I) (X : ISet I) → Set
UncurriedElᴰ D X = ∀{i} → Elᴰ D X i → X i

CurriedElᴰ : {I : Set} (D : Desc I) (X : ISet I) → Set
CurriedElᴰ (End i) X = X i
CurriedElᴰ (Rec i D) X = (x : X i) → CurriedElᴰ D X
CurriedElᴰ (Arg A B) X = (a : A) → CurriedElᴰ (B a) X

curryElᴰ : {I : Set} (D : Desc I) (X : ISet I)
  → UncurriedElᴰ D X → CurriedElᴰ D X
curryElᴰ (End i) X cn = cn refl
curryElᴰ (Rec i D) X cn = λ x → curryElᴰ D X (λ xs → cn (x , xs))
curryElᴰ (Arg A B) X cn = λ a → curryElᴰ (B a) X (λ xs → cn (a , xs))

----------------------------------------------------------------------

injUncurried : (R : Data)
  → UncurriedElᵀ (Data.P R) λ A
  → let D = Data.D R A
  in CurriedElᴰ D (μ D)
injUncurried R A t =
  curryElᴰ (Data.C R A t) (μ (Data.D R A))
    (λ xs → init (t , xs))

inj : (R : Data)
  → ICurriedElᵀ (Data.P R) λ p
  → let D = Data.D R p
  in CurriedElᴰ D (μ D)
inj R =
  icurryElᵀ (Data.P R) (λ p → let D = Data.D R p in CurriedElᴰ D (μ D))
    (injUncurried R)

----------------------------------------------------------------------

FormUncurried : (R : Data)
  → UncurriedElᵀ (Data.P R) λ p
  → UncurriedElᵀ (Data.I R p) λ i
  → Set
FormUncurried R p i = μ (Data.D R p) i

Form : (R : Data)
  → CurriedElᵀ (Data.P R) λ p
  → CurriedElᵀ (Data.I R p) λ i
  → Set
Form R =
  curryElᵀ (Data.P R) (λ p → CurriedElᵀ (Data.I R p) λ i → Set) λ p →
  curryElᵀ (Data.I R p) (λ i → Set) λ i →
  FormUncurried R p i

----------------------------------------------------------------------

ℕE : Enum
ℕE = "zero" ∷ "suc" ∷ []

VecE : Enum
VecE = "nil" ∷ "cons" ∷ []

ℕT : Set
ℕT = Tag ℕE

VecT : Set
VecT = Tag VecE

zeroT : ℕT
zeroT = here

sucT : ℕT
sucT = there here

nilT : VecT
nilT = here

consT : VecT
consT = there here

ℕR : Data
ℕR = record
  { P = End
  ; I = λ _ → End
  ; E = ℕE
  ; B = λ _ →
      End tt
    , Rec tt (End tt)
    , tt
  }

ℕ : Set
ℕ = Form ℕR

zero : ℕ
zero = inj ℕR zeroT

suc : ℕ → ℕ
suc = inj ℕR sucT

VecR : Data
VecR = record
  { P = Arg Set (λ _ → End)
  ; I = λ _ → Arg ℕ (λ _ → End)
  ; E = VecE
  ; B = λ A →
      End (zero , tt)
    , Arg ℕ (λ n → Arg (proj₁ A) λ _ → Rec (n , tt) (End (suc n , tt)))
    , tt
  }

Vec : (A : Set) → ℕ → Set
Vec = Form VecR

nil : {A : Set} → Vec A zero
nil = inj VecR nilT

cons : {A : Set} (n : ℕ) (x : A) (xs : Vec A n) → Vec A (suc n)
cons = inj VecR consT

----------------------------------------------------------------------

