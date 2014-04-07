{-# OPTIONS --type-in-type #-}
open import Spire.DarkwingDuck.Primitive
module Spire.DarkwingDuck.Derived where

----------------------------------------------------------------------

ISet : Set → Set
ISet I = I → Set

Enum : Set
Enum = List String

Tag : Enum → Set
Tag xs = Point String xs

proj₁ : ∀{A B} → Σ A B → A
proj₁ = elimPair _ (λ a b → a)

proj₂ : ∀{A B} (ab : Σ A B) → B (proj₁ ab)
proj₂ = elimPair _ (λ a b → b)

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

Elᵀ  : Tel → Set
Elᵀ = elimTel _ ⊤ (λ A B ih → Σ A ih) (λ A B ih → Σ A ih)

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
  (λ A B ih X → {a : A} → ih a (λ b → X (a , b)))

curryElᵀ : (T : Tel) (X : Elᵀ T → Set)
  → UncurriedElᵀ T X → CurriedElᵀ T X
curryElᵀ = elimTel _
  (λ X f → f tt)
  (λ A B ih X f a → ih a (λ b → X (a , b)) (λ b → f (a , b)))
  (λ A B ih X f {a} → ih a (λ b → X (a , b)) (λ b → f (a , b)))

uncurryElᵀ : (T : Tel) (X : Elᵀ T → Set)
  → CurriedElᵀ T X → UncurriedElᵀ T X
uncurryElᵀ = elimTel _
  (λ X x → elimUnit X x)
  (λ A B ih X f → elimPair X (λ a b → ih a (λ b → X (a , b)) (f a) b))
  (λ A B ih X f → elimPair X (λ a b → ih a (λ b → X (a , b)) f b))

ICurriedElᵀ : (T : Tel) (X : Elᵀ T → Set) → Set
ICurriedElᵀ = elimTel _
  (λ X → X tt)
  (λ A B ih X → {a : A} → ih a (λ b → X (a , b)))
  (λ A B ih X → {a : A} → ih a (λ b → X (a , b)))

icurryElᵀ : (T : Tel) (X : Elᵀ T → Set)
  → UncurriedElᵀ T X → ICurriedElᵀ T X
icurryElᵀ = elimTel _
  (λ X f → f tt)
  (λ A B ih X f {a} → ih a (λ b → X (a , b)) (λ b → f (a , b)))
  (λ A B ih X f {a} → ih a (λ b → X (a , b)) (λ b → f (a , b)))

----------------------------------------------------------------------

UncurriedElᴰ : {I : Set} (D : Desc I) (X : ISet I) → Set
UncurriedElᴰ D X = ∀{i} → Elᴰ D X i → X i

CurriedElᴰ : {I : Set} (D : Desc I) (X : ISet I) → Set
CurriedElᴰ = elimDesc _
  (λ i X → X i)
  (λ i D ih X → (x : X i) → ih X )
  (λ A B ih X → (a : A) → ih a X)
  (λ A B ih X → {a : A} → ih a X)

curryElᴰ : {I : Set} (D : Desc I) (X : ISet I)
  → UncurriedElᴰ D X → CurriedElᴰ D X
curryElᴰ = elimDesc _
  (λ i X cn → cn refl)
  (λ i D ih X cn x → ih X (λ xs → cn (x , xs)))
  (λ A B ih X cn a → ih a X (λ xs → cn (a , xs)))
  (λ A B ih X cn {a} → ih a X (λ xs → cn (a , xs)))

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
  (λ A B ih X P cn → {a : A} → ih a X P (λ xs → cn (a , xs)))

uncurryHyps : {I : Set} (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedElᴰ D X)
  → CurriedHyps D X P cn
  → UncurriedHyps D X P cn
uncurryHyps = elimDesc _
  (λ j X P cn pf →
    elimEq _ (λ u → pf))
  (λ j D ih X P cn pf i →
    elimPair _ (λ x xs ih,ihs →
      ih X P (λ ys → cn (x , ys)) (pf x (proj₁ ih,ihs)) i xs (proj₂ ih,ihs)))
  (λ A B ih X P cn pf i →
    elimPair _ (λ a xs → ih a X P (λ ys → cn (a , ys)) (pf a) i xs))
  (λ A B ih X P cn pf i →
    elimPair _ (λ a xs → ih a X P (λ ys → cn (a , ys)) pf i xs))

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

Decl :
  (E : Enum)
  (P : Tel)
  (I : CurriedElᵀ P (λ _ → Tel))
  (B : let I = uncurryElᵀ P (λ _ → Tel) I
      in CurriedElᵀ P λ A → Branches E (λ _ → Desc (Elᵀ (I A))))
  → Data
Decl E P I B = record
  { P = P
  ; I = uncurryElᵀ P _ I
  ; E = E
  ; B = uncurryElᵀ P _ B
  }

----------------------------------------------------------------------

End[_] : (I : Tel)
  → CurriedElᵀ I (λ _ → Desc (Elᵀ I))
End[_] I = curryElᵀ I _ End

Rec[_] : (I : Tel)
  → CurriedElᵀ I (λ _ → Desc (Elᵀ I) → Desc (Elᵀ I))
Rec[_] I = curryElᵀ I _ Rec

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
