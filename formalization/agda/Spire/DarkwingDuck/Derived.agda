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
  (λ j X P cn pf i q u → elimEq I j
   (λ k r → P k (cn k r))
   pf i q
  )
  (λ j D ih X P cn pf i → elimPair (X j)
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
  (λ A B ih X P cn pf i → elimPair A
    (λ a → Func I (B a) X i)
    (λ xs → Hyps I (Arg A (λ a → B a)) X P i xs → P i (cn i xs))
    (λ a xs → ih a X P (λ j ys → cn j (a , ys))
      (pf a) i xs
    )
  )

----------------------------------------------------------------------

BranchesD : Enum → Tel → Set
BranchesD E T = Branches E (λ _ → Desc (Scope T))

caseD : (E : Enum) (T : Tel) (cs : BranchesD E T) (t : Tag E) → Desc (Scope T)
caseD E T = case E (λ _ → Desc (Scope T))

sumD : (E : Enum) (T : Tel) (cs : BranchesD E T) → Desc (Scope T)
sumD E T cs = Arg (Tag E) (λ t → caseD E T cs t)

ITel : Tel → Set
ITel P = Scope P → Tel

itel : (P : Tel) → CurriedScope P (λ _ → Tel) → ITel P
itel P I = uncurryScope P (λ p → Tel) I

IBranches : (E : Enum) (P : Tel) (I : ITel P) → Set
IBranches E P I = (p : Scope P) → BranchesD E (I p)

ibranches : (E : Enum) (P : Tel) (I : ITel P) → CurriedScope P (λ p → BranchesD E (I p)) → IBranches E P I
ibranches E P I B = uncurryScope P (λ p → BranchesD E (I p)) B

Data : (X : (N : String) (E : Enum) (P : Tel) (I : ITel P) (B : IBranches E P I) → Set)
  → Set
Data X = (N : String) (E : Enum) (P : Tel) (I : ITel P) (B : IBranches E P I)
  → X N E P I B

----------------------------------------------------------------------

FormUncurried : Data λ N E P I B
  → UncurriedScope P λ p
  → UncurriedScope (I p) λ i
  → Set
FormUncurried N E P I B p =
  μ N (Scope P) (Scope (I p)) (sumD E (I p) (B p)) p

FORM : (P : Tel) → ITel P → Set
FORM P I = CurriedScope P λ p → CurriedScope (I p) λ i → Set

Form : Data λ N E P I B → FORM P I
Form N E P I B =
  curryScope P (λ p → CurriedScope (I p) λ i → Set) λ p →
  curryScope (I p) (λ i → Set) λ i →
  FormUncurried N E P I B p i

----------------------------------------------------------------------

injUncurried : Data λ N E P I B
  → (t : Tag E)
  → UncurriedScope P λ p
  → CurriedFunc (Scope (I p)) (caseD E (I p) (B p) t) (FormUncurried N E P I B p)
injUncurried N E P I B t p = curryFunc (Scope (I p)) (caseD E (I p) (B p) t)
  (FormUncurried N E P I B p)
  (λ i xs → init (t , xs))

Inj : Data λ N E P I B → (t : Tag E) → Set
Inj N E P I B t = CurriedScope P λ p
  → CurriedFunc (Scope (I p)) (caseD E (I p) (B p) t) (FormUncurried N E P I B p)

inj : Data λ N E P I B
  → (t : Tag E)
  → Inj N E P I B t
inj N E P I B t = curryScope P
  (λ p → CurriedFunc (Scope (I p)) (caseD E (I p) (B p) t) (FormUncurried N E P I B p))
  (injUncurried N E P I B t)

----------------------------------------------------------------------

indCurried : (ℓ : String) (P I : Set) (D : Desc I) (p : P)
  (M : (i : I) → μ ℓ P I D p i → Set)
  (f : CurriedHyps I D (μ ℓ P I D p) M (λ _ xs → init xs))
  (i : I) (x : μ ℓ P I D p i) → M i x
indCurried ℓ P I D p M f i x =
  ind ℓ P I D p M (uncurryHyps I D (μ ℓ P I D p) M (λ _ xs → init xs) f) i x

SumCurriedHyps : Data λ N E P I B
  → UncurriedScope P λ p
  → (M : CurriedScope (I p) (λ i → FormUncurried N E P I B p i → Set))
  → Tag E → Set
SumCurriedHyps N E P I B p M t =
  let unM = uncurryScope (I p) (λ i → FormUncurried N E P I B p i → Set) M in
  CurriedHyps (Scope (I p)) (caseD E (I p) (B p) t)
    (FormUncurried N E P I B p) unM (λ i xs → init (t , xs))

elimUncurried : Data λ N E P I B
  → UncurriedScope P λ p
  → (M : CurriedScope (I p) (λ i → FormUncurried N E P I B p i → Set))
  → let unM = uncurryScope (I p) (λ i → FormUncurried N E P I B p i → Set) M
  in UncurriedBranches E
     (SumCurriedHyps N E P I B p M)
     (CurriedScope (I p) (λ i → (x : FormUncurried N E P I B p i) → unM i x))
elimUncurried N E P I B p M cs = let
    unM = uncurryScope (I p) (λ i → FormUncurried N E P I B p i → Set) M
  in
  curryScope (I p) (λ i → (x : FormUncurried N E P I B p i) → unM i x)
  (indCurried N (Scope P) (Scope (I p)) (sumD E (I p) (B p)) p unM
    (case E (SumCurriedHyps N E P I B p M) cs))

Elim : Data λ N E P I B → Set
Elim N E P I B = CurriedScope P λ p
  → (M : CurriedScope (I p) (λ i → FormUncurried N E P I B p i → Set))
  → let unM = uncurryScope (I p) (λ i → FormUncurried N E P I B p i → Set) M
  in CurriedBranches E
     (SumCurriedHyps N E P I B p M)
     (CurriedScope (I p) (λ i → (x : FormUncurried N E P I B p i) → unM i x))

elim : Data λ N E P I B → Elim N E P I B
elim N E P I B = curryScope P
  (λ p → (M : CurriedScope (I p) (λ i → FormUncurried N E P I B p i → Set))
    → let unM = uncurryScope (I p) (λ i → FormUncurried N E P I B p i → Set) M
    in CurriedBranches E
       (SumCurriedHyps N E P I B p M)
       (CurriedScope (I p) (λ i → (x : FormUncurried N E P I B p i) → unM i x)))
  (λ p M → let unM = uncurryScope (I p) (λ i → FormUncurried N E P I B p i → Set) M
    in curryBranches E
    (SumCurriedHyps N E P I B p M)
    (CurriedScope (I p) (λ i → (x : FormUncurried N E P I B p i) → unM i x))
    (elimUncurried N E P I B p M))

----------------------------------------------------------------------
