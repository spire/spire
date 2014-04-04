{-# OPTIONS --type-in-type #-}
open import Spire.Examples.DarkwingDuck.Primitive
module Spire.Examples.DarkwingDuck.Derived where

----------------------------------------------------------------------

Enum : Set
Enum = List String

ISet : Set → Set
ISet I = I → Set

----------------------------------------------------------------------

record Data : Set where
  field
    P : Tel
    I : Elᵀ P → Tel
    E : Enum
    B : (A : Elᵀ P) → Branches E (λ _ → Desc (Elᵀ (I A)))

  C : (A : Elᵀ P) → Tag E → Desc (Elᵀ (I A))
  C A = case (λ _ → Desc (Elᵀ (I A))) (B A)

  D : (A : Elᵀ P) → Desc (Elᵀ (I A))
  D A = Arg (Tag E) (C A)

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

uncurryElᵀ : (T : Tel) (X : Elᵀ T → Set)
  → CurriedElᵀ T X → UncurriedElᵀ T X
uncurryElᵀ End X x tt = x
uncurryElᵀ (Arg A B) X f (a , b) = uncurryElᵀ (B a) (λ b → X (a , b)) (f a) b

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

UncurriedHyps : {I : Set} (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedElᴰ D X)
  → Set
UncurriedHyps D X P cn =
  ∀ i (xs : Elᴰ D X i) (ihs : Hyps D X P i xs) → P i (cn xs)

CurriedHyps : {I : Set} (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedElᴰ D X)
  → Set
CurriedHyps (End i) X P cn =
  P i (cn refl)
CurriedHyps (Rec i D) X P cn =
  (x : X i) → P i x → CurriedHyps D X P (λ xs → cn (x , xs))
CurriedHyps (Arg A B) X P cn =
  (a : A) → CurriedHyps (B a) X P (λ xs → cn (a , xs))

curryHyps : {I : Set} (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedElᴰ D X)
  → UncurriedHyps D X P cn
  → CurriedHyps D X P cn
curryHyps (End i) X P cn pf =
  pf i refl tt
curryHyps (Rec i D) X P cn pf =
  λ x ih → curryHyps D X P (λ xs → cn (x , xs)) (λ i xs ihs → pf i (x , xs) (ih , ihs))
curryHyps (Arg A B) X P cn pf =
  λ a → curryHyps (B a) X P (λ xs → cn (a , xs)) (λ i xs ihs → pf i (a , xs) ihs)

uncurryHyps : {I : Set} (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedElᴰ D X)
  → CurriedHyps D X P cn
  → UncurriedHyps D X P cn
uncurryHyps (End .i) X P cn pf i refl tt =
  pf
uncurryHyps (Rec j D) X P cn pf i (x , xs) (ih , ihs) =
  uncurryHyps D X P (λ ys → cn (x , ys)) (pf x ih) i xs ihs
uncurryHyps (Arg A B) X P cn pf i (a , xs) ihs =
  uncurryHyps (B a) X P (λ ys → cn (a , ys)) (pf a) i xs ihs

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

injUncurried : (R : Data)
  → UncurriedElᵀ (Data.P R) λ p
  → let D = Data.D R p
  in CurriedElᴰ D (μ D)
injUncurried R p t = curryElᴰ (Data.C R p t)
  (μ (Data.D R p))
  (λ xs → init (t , xs))

inj : (R : Data)
  → ICurriedElᵀ (Data.P R) λ p
  → let D = Data.D R p
  in CurriedElᴰ D (μ D)
inj R = icurryElᵀ (Data.P R)
  (λ p → let D = Data.D R p in CurriedElᴰ D (μ D))
  (injUncurried R)

----------------------------------------------------------------------

indCurried : {I : Set} (D : Desc I)
  (M : (i : I) → μ D i → Set)
  (f : CurriedHyps D (μ D) M init)
  (i : I)
  (x : μ D i)
  → M i x
indCurried D M f i x =
  ind D M (uncurryHyps D (μ D) M init f) i x

SumCurriedHyps : (R : Data)
  → UncurriedElᵀ (Data.P R) λ p
  → let D = Data.D R p in
  (M : CurriedElᵀ (Data.I R p) (λ i → μ D i → Set))
  → Tag (Data.E R) → Set
SumCurriedHyps R p M t =
  let unM = uncurryElᵀ (Data.I R p) (λ i → μ (Data.D R p) i → Set) M in
  CurriedHyps (Data.C R p t) (μ (Data.D R p)) unM (λ xs → init (t , xs))

elimUncurried : (R : Data)
  → UncurriedElᵀ (Data.P R) λ p
  → let D = Data.D R p in
  (M : CurriedElᵀ (Data.I R p) (λ i → μ D i → Set))
  → let unM = uncurryElᵀ (Data.I R p) (λ i → μ D i → Set) M
  in UncurriedBranches (Data.E R)
     (SumCurriedHyps R p M)
     (CurriedElᵀ (Data.I R p) (λ i → (x : μ D i) → unM i x))
elimUncurried R p M cs =
  let D = Data.D R p
      unM = uncurryElᵀ (Data.I R p) (λ i → μ D i → Set) M
  in
  curryElᵀ (Data.I R p) (λ i → (x : μ D i) → unM i x) λ i x →
  indCurried (Data.D R p) unM
    (case (SumCurriedHyps R p M) cs)
    i x

elim : (R : Data)
  → ICurriedElᵀ (Data.P R) λ p
  → let D = Data.D R p in
  (M : CurriedElᵀ (Data.I R p) (λ i → μ D i → Set))
  → let unM = uncurryElᵀ (Data.I R p) (λ i → μ D i → Set) M
  in CurriedBranches (Data.E R)
     (SumCurriedHyps R p M)
     (CurriedElᵀ (Data.I R p) (λ i → (x : μ D i) → unM i x))
elim R = icurryElᵀ (Data.P R)
  (λ p → let D = Data.D R p in
    (M : CurriedElᵀ (Data.I R p) (λ i → μ D i → Set))
    → let unM = uncurryElᵀ (Data.I R p) (λ i → μ D i → Set) M
    in CurriedBranches (Data.E R)
       (SumCurriedHyps R p M)
       (CurriedElᵀ (Data.I R p) (λ i → (x : μ D i) → unM i x)))
  (λ p M → curryBranches
    (elimUncurried R p M))

----------------------------------------------------------------------
