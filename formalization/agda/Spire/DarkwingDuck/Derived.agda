{-# OPTIONS --type-in-type --no-pattern-matching #-}
open import Spire.DarkwingDuck.Primitive
module Spire.DarkwingDuck.Derived where

----------------------------------------------------------------------

subst : (A : Set) (x : A) (y : A) (P : A → Set) → P x → x ≡ y → P y
subst A x y P p = elimEq A x (λ y _ → P y) p y

ISet : Set → Set
ISet I = I → Set

Scope  : Tel → Set
Scope = elimTel (λ _ → Set) ⊤ (λ A B ih → Σ A ih)

----------------------------------------------------------------------

UncurriedBranches : (E : Enum) (P : Tag E → Set) (X : Set)
  → Set
UncurriedBranches E P X = Branches E P → X

CurriedBranchesM : Enum → Set
CurriedBranchesM E = (P : Tag E → Set) (X : Set) → Set

CurriedBranches : (E : Enum) → CurriedBranchesM E
CurriedBranches = elimEnum CurriedBranchesM
  (λ P X → X)
  (λ l E ih P X → P here → ih (λ t → P (there t)) X)

CurryBranches : Enum → Set
CurryBranches E = (P : Tag E → Set) (X : Set) → UncurriedBranches E P X → CurriedBranches E P X

curryBranches : (E : Enum) → CurryBranches E
curryBranches = elimEnum CurryBranches
  (λ P X f → f tt)
  (λ l E ih P X f c → ih (λ t → P (there t)) X (λ cs → f (c , cs)))

----------------------------------------------------------------------

UncurriedScope : (T : Tel) (X : Scope T → Set) → Set
UncurriedScope T X = (xs : Scope T) → X xs

CurriedScope : (T : Tel) (X : Scope T → Set) → Set
CurriedScope = elimTel
  (λ T → (X : Scope T → Set) → Set)
  (λ X → X tt)
  (λ A B ih X → (a : A) → ih a (λ b → X (a , b)))

CurryScope : Tel → Set
CurryScope T = (X : Scope T → Set) → UncurriedScope T X → CurriedScope T X

curryScope : (T : Tel) → CurryScope T
curryScope = elimTel CurryScope
  (λ X f → f tt)
  (λ A B ih X f a → ih a (λ b → X (a , b)) (λ b → f (a , b)))

UncurryScope : Tel → Set
UncurryScope T = (X : Scope T → Set) → CurriedScope T X → UncurriedScope T X

uncurryScope : (T : Tel) → UncurryScope T
uncurryScope = elimTel UncurryScope
  (λ X x → elimUnit X x)
  (λ A B ih X f → elimPair A (λ a → Scope (B a)) X (λ a b → ih a (λ b → X (a , b)) (f a) b))

----------------------------------------------------------------------

UncurriedFunc : (I : Set) (D : Desc I) (X : ISet I) → Set
UncurriedFunc I D X = (i : I) → Func I D X i → X i

CurriedFuncM : (I : Set) → Desc I → Set
CurriedFuncM I _ = (X : ISet I) → Set

CurriedFunc : (I : Set) (D : Desc I) (X : ISet I) → Set
CurriedFunc I = elimDesc I (CurriedFuncM I)
  (λ i X → X i)
  (λ i D ih X → (x : X i) → ih X)
  (λ A B ih X → (a : A) → ih a X)

CurryFunc : (I : Set) → Desc I → Set
CurryFunc I D = (X : ISet I) → UncurriedFunc I D X → CurriedFunc I D X

curryFunc : (I : Set) (D : Desc I) → CurryFunc I D
curryFunc I = elimDesc I (CurryFunc I)
  (λ i X cn → cn i refl)
  (λ i D ih X cn x → ih X (λ j xs → cn j (x , xs)))
  (λ A B ih X cn a → ih a X (λ j xs → cn j (a , xs)))

----------------------------------------------------------------------

UncurriedHyps : (I : Set) (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedFunc I D X)
  → Set
UncurriedHyps I D X P cn =
  (i : I) (xs : Func I D X i) (ihs : Hyps I D X P i xs) → P i (cn i xs)

CurriedHypsM : (I : Set) (D : Desc I) → Set
CurriedHypsM I D = (X : ISet I) (P : (i : I) → X i → Set) (cn : UncurriedFunc I D X) → Set

CurriedHyps : (I : Set) (D : Desc I) → CurriedHypsM I D
CurriedHyps I = elimDesc I (CurriedHypsM I)
  (λ i X P cn → P i (cn i refl))
  (λ i D ih X P cn → (x : X i) → P i x → ih X P (λ j xs → cn j (x , xs)))
  (λ A B ih X P cn → (a : A) → ih a X P (λ j xs → cn j (a , xs)))

UncurryHyps : (I : Set) (D : Desc I) → Set
UncurryHyps I D = (X : ISet I) (P : (i : I) → X i → Set) (cn : UncurriedFunc I D X)
  → CurriedHyps I D X P cn → UncurriedHyps I D X P cn

uncurryHyps : (I : Set) (D : Desc I) → UncurryHyps I D
uncurryHyps I = elimDesc I (UncurryHyps I)
  (λ j X P cn pf i q u →
    elimEq I j (λ k r → P k (cn k r))
      pf i q)
  (λ j D ih X P cn pf i →
    elimPair (X j)
      (λ _ → Func I D X i)
      (λ xs → Hyps I (Rec j D) X P i xs → P i (cn i xs))
      (λ x xs → elimPair (P j x)
        (λ _ → Hyps I D X P i xs)
        (λ _ → P i (cn i (x , xs)))
        (λ p ps → ih X P (λ j ys → cn j (x , ys))
          (pf x p) i xs ps
        )
      )
   )
  (λ A B ih X P cn pf i →
    elimPair A
      (λ a → Func I (B a) X i)
      (λ xs → Hyps I (Arg A B) X P i xs → P i (cn i xs))
      (λ a xs →
        ih a X P (λ j ys → cn j (a , ys))
          (pf a)
          i xs
      )
  )

----------------------------------------------------------------------

record Data : Set where
  field
    N : String
    P : Tel
    I : Scope P → Tel
    E : Enum
    B : (p : Scope P) → Branches E (λ _ → Desc (Scope (I p)))

  PS : Set
  PS = Scope P

  IS : PS → Set
  IS p = Scope (I p)

  C : (p : PS) → Tag E → Desc (IS p)
  C p = case E (λ _ → Desc (IS p)) (B p)

  D : (p : PS) → Desc (IS p)
  D p = Arg (Tag E) (C p)

  F : (p : PS) → IS p → Set
  F p = μ N PS (IS p) (D p) p

----------------------------------------------------------------------

Decl :
  (N : String)
  (P : Tel)
  (I : CurriedScope P (λ _ → Tel))
  (E : Enum)
  (B : let I = uncurryScope P (λ _ → Tel) I
      in CurriedScope P λ A → Branches E (λ _ → Desc (Scope (I A))))
  → Data
Decl N P I E B = record
  { N = N
  ; P = P
  ; I = uncurryScope P _ I
  ; E = E
  ; B = uncurryScope P _ B
  }

----------------------------------------------------------------------

End[_] : (I : Tel)
  → CurriedScope I (λ _ → Desc (Scope I))
End[_] I = curryScope I _ End

Rec[_] : (I : Tel)
  → CurriedScope I (λ _ → Desc (Scope I) → Desc (Scope I))
Rec[_] I = curryScope I _ Rec

----------------------------------------------------------------------

FormUncurried : (R : Data)
  → UncurriedScope (Data.P R) λ p
  → UncurriedScope (Data.I R p) λ i
  → Set
FormUncurried = Data.F

Form : (R : Data)
  → CurriedScope (Data.P R) λ p
  → CurriedScope (Data.I R p) λ i
  → Set
Form R =
  curryScope (Data.P R) (λ p → CurriedScope (Data.I R p) λ i → Set) λ p →
  curryScope (Data.I R p) (λ i → Set) λ i →
  FormUncurried R p i

----------------------------------------------------------------------

injUncurried : (R : Data)
  → UncurriedScope (Data.P R) λ p
  → CurriedFunc (Data.IS R p) (Data.D R p) (Data.F R p)
injUncurried R p t = curryFunc (Data.IS R p) (Data.C R p t)
  (Data.F R p)
  (λ i xs → init (t , xs))

inj : (R : Data)
  → CurriedScope (Data.P R) λ p
  → CurriedFunc (Data.IS R p) (Data.D R p) (Data.F R p)
inj R = curryScope (Data.P R)
  (λ p → CurriedFunc (Data.IS R p) (Data.D R p) (Data.F R p))
  (injUncurried R)

----------------------------------------------------------------------

indCurried : (ℓ : String) (P I : Set) (D : Desc I) (p : P)
  (M : (i : I) → μ ℓ P I D p i → Set)
  (f : CurriedHyps I D (μ ℓ P I D p) M (λ _ → init))
  (i : I) (x : μ ℓ P I D p i) → M i x
indCurried ℓ P I D p M f i x =
  ind ℓ P I D p M (uncurryHyps I D (μ ℓ P I D p) M (λ _ → init) f) i x

SumCurriedHyps : (R : Data)
  → UncurriedScope (Data.P R) λ p
  → (M : CurriedScope (Data.I R p) (λ i → Data.F R p i → Set))
  → Tag (Data.E R) → Set
SumCurriedHyps R p M t =
  let unM = uncurryScope (Data.I R p) (λ i → Data.F R p i → Set) M in
  CurriedHyps (Data.IS R p) (Data.C R p t) (Data.F R p) unM (λ i xs → init (t , xs))

elimUncurried : (R : Data)
  → UncurriedScope (Data.P R) λ p
  → (M : CurriedScope (Data.I R p) (λ i → Data.F R p i → Set))
  → let unM = uncurryScope (Data.I R p) (λ i → Data.F R p i → Set) M
  in UncurriedBranches (Data.E R)
     (SumCurriedHyps R p M)
     (CurriedScope (Data.I R p) (λ i → (x : Data.F R p i) → unM i x))
elimUncurried R p M cs = let
    unM = uncurryScope (Data.I R p) (λ i → Data.F R p i → Set) M
  in
  curryScope (Data.I R p) (λ i → (x : Data.F R p i) → unM i x) λ i x →
  indCurried (Data.N R) (Data.PS R) (Data.IS R p) (Data.D R p) p unM
    (case (Data.E R) (SumCurriedHyps R p M) cs)
    i x

elim : (R : Data)
  → CurriedScope (Data.P R) λ p
  → (M : CurriedScope (Data.I R p) (λ i → Data.F R p i → Set))
  → let unM = uncurryScope (Data.I R p) (λ i → Data.F R p i → Set) M
  in CurriedBranches (Data.E R)
     (SumCurriedHyps R p M)
     (CurriedScope (Data.I R p) (λ i → (x : Data.F R p i) → unM i x))
elim R = curryScope (Data.P R)
  (λ p → (M : CurriedScope (Data.I R p) (λ i → Data.F R p i → Set))
    → let unM = uncurryScope (Data.I R p) (λ i → Data.F R p i → Set) M
    in CurriedBranches (Data.E R)
       (SumCurriedHyps R p M)
       (CurriedScope (Data.I R p) (λ i → (x : Data.F R p i) → unM i x)))
  (λ p M → curryBranches (Data.E R) _ _
    (elimUncurried R p M))

----------------------------------------------------------------------
