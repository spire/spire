{-# OPTIONS --type-in-type #-}
open import Spire.Examples.DarkwingDuck.Primitive
module Spire.Examples.DarkwingDuck.Derived where

----------------------------------------------------------------------

ISet : Set → Set
ISet I = I → Set

Enum : Set
Enum = List String

Tag : Enum → Set
Tag xs = Point String xs

Branches : (E : List String) (P : Tag E → Set) → Set
Branches = elimList _
  (λ P → ⊤)
  (λ l E ih P → Σ (P here) (λ _ → ih (λ t → P (there t))))

case' : (E : List String) (t : Tag E) (P : Tag E → Set) (cs : Branches E P) → P t
case' = elimPoint _
  (λ l E P c,cs → proj₁ c,cs)
  (λ l E t ih P c,cs → ih (λ t → P (there t)) (proj₂ c,cs))

case : {E : List String} (P : Tag E → Set) (cs : Branches E P) (t : Tag E) → P t
case P cs t = case' _ t P cs

----------------------------------------------------------------------

Elᵀ  : Tel → Set
Elᵀ = elimTel _
  ⊤
  (λ A B ih → Σ A ih)

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
CurriedBranches = elimList _
  (λ P X → X)
  (λ l E ih P X → P here → ih (λ t → P (there t)) X)

curryBranches : (E : Enum) (P : Tag E → Set) (X : Set)
  → UncurriedBranches E P X → CurriedBranches E P X
curryBranches = elimList _
  (λ P X f → f tt)
  (λ l E ih P X f c → ih (λ t → P (there t)) X (λ cs → f (c , cs)))

----------------------------------------------------------------------

UncurriedElᵀ : (T : Tel) (X : Elᵀ T → Set) → Set
UncurriedElᵀ T X = (xs : Elᵀ T) → X xs

CurriedElᵀ : (T : Tel) (X : Elᵀ T → Set) → Set
CurriedElᵀ = elimTel _
  (λ X → X tt)
  (λ A B ih X → (a : A) → ih a (λ b → X (a , b)))

curryElᵀ : (T : Tel) (X : Elᵀ T → Set)
  → UncurriedElᵀ T X → CurriedElᵀ T X
curryElᵀ = elimTel _
  (λ X f → f tt)
  (λ A B ih X f a → ih a (λ b → X (a , b)) (λ b → f (a , b)))

uncurryElᵀ : (T : Tel) (X : Elᵀ T → Set)
  → CurriedElᵀ T X → UncurriedElᵀ T X
-- uncurryElᵀ = elimTel _
--   (λ X x u → elimUnit X x u)
--   (λ A B ih X f a,b → {!!})
uncurryElᵀ End X x tt = x
uncurryElᵀ (Arg A B) X f (a , b) = uncurryElᵀ (B a) (λ b → X (a , b)) (f a) b

ICurriedElᵀ : (T : Tel) (X : Elᵀ T → Set) → Set
ICurriedElᵀ = elimTel _
  (λ X → X tt)
  (λ A B ih X → {a : A} → ih a (λ b → X (a , b)))

icurryElᵀ : (T : Tel) (X : Elᵀ T → Set)
  → UncurriedElᵀ T X → ICurriedElᵀ T X
icurryElᵀ = elimTel _
  (λ X f → f tt)
  (λ A B ih X f {a} → ih a (λ b → X (a , b)) (λ b → f (a , b)))

----------------------------------------------------------------------

UncurriedElᴰ : {I : Set} (D : Desc I) (X : ISet I) → Set
UncurriedElᴰ D X = ∀{i} → Elᴰ D X i → X i

CurriedElᴰ : {I : Set} (D : Desc I) (X : ISet I) → Set
CurriedElᴰ = elimDesc _
  (λ i X → X i)
  (λ i D ih X → (x : X i) → ih X )
  (λ A B ih X → (a : A) → ih a X)

curryElᴰ : {I : Set} (D : Desc I) (X : ISet I)
  → UncurriedElᴰ D X → CurriedElᴰ D X
curryElᴰ = elimDesc _
  (λ i X cn → cn refl)
  (λ i D ih X cn x → ih X (λ xs → cn (x , xs)))
  (λ A B ih X cn a → ih a X (λ xs → cn (a , xs)))

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
CurriedHyps = elimDesc _
  (λ i X P cn → P i (cn refl))
  (λ i D ih X P cn → (x : X i) → P i x → ih X P (λ xs → cn (x , xs)))
  (λ A B ih X P cn → (a : A) → ih a X P (λ xs → cn (a , xs)))

uncurryHyps : {I : Set} (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedElᴰ D X)
  → CurriedHyps D X P cn
  → UncurriedHyps D X P cn
-- uncurryHyps = elimDesc _
--   (λ j X P cn pf i q u →
--     elimEq (λ k q → P k (cn q)) pf i q)
--   (λ j D ih X P cn pf i x,xs ih,ihs →
--     {!!})
--   (λ A B ih X P cn pf i a,xs ihs →
--     {!!})
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
  (λ p M → curryBranches (Data.E R) _ _
    (elimUncurried R p M))

----------------------------------------------------------------------
