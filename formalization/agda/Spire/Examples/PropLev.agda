{-# OPTIONS --type-in-type #-}
open import Data.Unit
open import Data.Product hiding ( curry ; uncurry )
open import Data.List hiding ( concat )
open import Data.String
open import Relation.Binary.PropositionalEquality
open import Function
module Spire.Examples.PropLev where

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

data Desc (I : Set) : Set₁ where
  End : (i : I) → Desc I
  Rec : (i : I) (D : Desc I) → Desc I
  Arg : (A : Set) (B : A → Desc I) → Desc I

elimDesc : {I : Set} (P : Desc I → Set)
  (pend : (i : I) → P (End i))
  (prec : (i : I) (D : Desc I) (pd : P D) → P (Rec i D))
  (parg : (A : Set) (B : A → Desc I) (pb : (a : A) → P (B a)) → P (Arg A B))
  (D : Desc I) → P D
elimDesc P pend prec parg (End i) = pend i
elimDesc P pend prec parg (Rec i D) = prec i D (elimDesc P pend prec parg D)
elimDesc P pend prec parg (Arg A B) = parg A B (λ a → elimDesc P pend prec parg (B a))

----------------------------------------------------------------------

ISet : Set → Set₁
ISet I = I → Set

El : {I : Set} (D : Desc I) → ISet I → ISet I
El (End j) X i = j ≡ i
El (Rec j D) X i = X j × El D X i
El (Arg A B) X i = Σ A (λ a → El (B a) X i)

Hyps : {I : Set} (D : Desc I) (X : ISet I) (P : (i : I) → X i → Set) (i : I) (xs : El D X i) → Set
Hyps (End j) X P i q = ⊤
Hyps (Rec j D) X P i (x , xs) = P j x × Hyps D X P i xs
Hyps (Arg A B) X P i (a , b) = Hyps (B a) X P i b

----------------------------------------------------------------------

UncurriedEl : {I : Set} (D : Desc I) (X : ISet I) → Set
UncurriedEl D X = ∀{i} → El D X i → X i

CurriedEl : {I : Set} (D : Desc I) (X : ISet I) → Set
CurriedEl (End i) X = X i
CurriedEl (Rec i D) X = (x : X i) → CurriedEl D X
CurriedEl (Arg A B) X = (a : A) → CurriedEl (B a) X

CurriedEl' : {I : Set} (D : Desc I) (X : ISet I) (i : I) → Set
CurriedEl' (End j) X i = j ≡ i → X i
CurriedEl' (Rec j D) X i = (x : X j) → CurriedEl' D X i
CurriedEl' (Arg A B) X i = (a : A) → CurriedEl' (B a) X i

curryEl : {I : Set} (D : Desc I) (X : ISet I)
  → UncurriedEl D X → CurriedEl D X
curryEl (End i) X cn = cn refl
curryEl (Rec i D) X cn = λ x → curryEl D X (λ xs → cn (x , xs))
curryEl (Arg A B) X cn = λ a → curryEl (B a) X (λ xs → cn (a , xs))

uncurryEl : {I : Set} (D : Desc I) (X : ISet I)
  → CurriedEl D X → UncurriedEl D X
uncurryEl (End i) X cn refl = cn
uncurryEl (Rec i D) X cn (x , xs) = uncurryEl D X (cn x) xs
uncurryEl (Arg A B) X cn (a , xs) = uncurryEl (B a) X (cn a) xs

----------------------------------------------------------------------

UncurriedHyps : {I : Set} (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedEl D X)
  → Set
UncurriedHyps D X P cn =
  ∀ i (xs : El D X i) (ihs : Hyps D X P i xs) → P i (cn xs)

CurriedHyps : {I : Set} (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedEl D X)
  → Set
CurriedHyps (End i) X P cn =
  P i (cn refl)
CurriedHyps (Rec i D) X P cn =
  (x : X i) → P i x → CurriedHyps D X P (λ xs → cn (x , xs))
CurriedHyps (Arg A B) X P cn =
  (a : A) → CurriedHyps (B a) X P (λ xs → cn (a , xs))

CurriedHyps' : {I : Set} (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (i : I)
  (cn : El D X i → X i)
  → Set
CurriedHyps' (End j) X P i cn = (q : j ≡ i) → P i (cn q)
CurriedHyps' (Rec j D) X P i cn =
  (x : X j) → P j x → CurriedHyps' D X P i (λ xs → cn (x , xs))
CurriedHyps' (Arg A B) X P i cn =
  (a : A) → CurriedHyps' (B a) X P i (λ xs → cn (a , xs))

curryHyps : {I : Set} (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedEl D X)
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
  (cn : UncurriedEl D X)
  → CurriedHyps D X P cn
  → UncurriedHyps D X P cn
uncurryHyps (End .i) X P cn pf i refl tt =
  pf
uncurryHyps (Rec j D) X P cn pf i (x , xs) (ih , ihs) =
  uncurryHyps D X P (λ ys → cn (x , ys)) (pf x ih) i xs ihs
uncurryHyps (Arg A B) X P cn pf i (a , xs) ihs =
  uncurryHyps (B a) X P (λ ys → cn (a , ys)) (pf a) i xs ihs

----------------------------------------------------------------------

data μ {I : Set} (D : Desc I) : ISet I where
  init : UncurriedEl D (μ D)

----------------------------------------------------------------------

Data : Set
Data =
  Σ Set λ I →
  Σ Enum λ E →
  Branches E (λ _ → Desc I)

DataI : Data → Set
DataI (I , E , B) = I

DataE : Data → Enum
DataE (I , E , B) = E

DataT : Data → Set
DataT R = Tag (DataE R)

DataB : (R : Data) → Branches (DataE R) (λ _ → Desc (DataI R))
DataB (I , E , B) = B

DataD : (R : Data) → Desc (DataI R)
DataD R = Arg (DataT R) (case (λ _ → Desc (DataI R)) (DataB R))

caseR : (R : Data) → DataT R → Desc (DataI R)
caseR R = case (λ _ → Desc (DataI R)) (DataB R)

----------------------------------------------------------------------

inj : (R : Data)
  → let D = DataD R
  in CurriedEl D (μ D)
inj R = let D = DataD R
  in curryEl D (μ D) init

----------------------------------------------------------------------

prove : {I : Set} (D : Desc I) (X : I → Set)
  (P : (i : I) → X i → Set)
  (α : (i : I) (x : X i) → P i x)
  (i : I) (xs : El D X i) → Hyps D X P i xs
prove (End j) X P α i q = tt
prove (Rec j D) X P α i (x , xs) = α j x , prove D X P α i xs
prove (Arg A B) X P α i (a , xs) = prove (B a) X P α i xs

{-# NO_TERMINATION_CHECK #-}
ind : {I : Set} (D : Desc I)
  (P : (i : I) → μ D i → Set)
  (α : UncurriedHyps D (μ D) P init)
  (i : I)
  (x : μ D i)
  → P i x
ind D P α i (init xs) = α i xs $
  prove D (μ D) P (ind D P α) i xs

----------------------------------------------------------------------

indCurried : {I : Set} (D : Desc I)
  (P : (i : I) → μ D i → Set)
  (f : CurriedHyps D (μ D) P init)
  (i : I)
  (x : μ D i)
  → P i x
indCurried D P f i x = ind D P (uncurryHyps D (μ D) P init f) i x

SumCurriedHyps : (R : Data)
  → let D = DataD R in
  (P : ∀ i → μ D i → Set)
  → DataT R → Set
SumCurriedHyps R P t =
  CurriedHyps (caseR R t) (μ (DataD R)) P (λ xs → init (t , xs))

elimUncurried : (R : Data)
  → let D = DataD R in
  (P : ∀ i → μ D i → Set)
  → Branches (DataE R) (SumCurriedHyps R P)
  → ∀ i (x : μ D i) → P i x
elimUncurried R P cs i x =
  indCurried (DataD R) P
    (case (SumCurriedHyps R P) cs)
    i x

elim : (R : Data)
  → let D = DataD R in
  (P : ∀ i → μ D i → Set)
  → CurriedBranches (DataE R)
      (SumCurriedHyps R P)
      (∀ i (x : μ D i) → P i x)
elim R P = curryBranches (elimUncurried R P)

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
ℕR = ⊤ , ℕE
  , End tt
  , Rec tt (End tt)
  , tt

ℕD : Desc ⊤
ℕD = DataD ℕR

ℕ : ⊤ → Set
ℕ = μ ℕD

zero : ℕ tt
zero = init (zeroT , refl)

suc : ℕ tt → ℕ tt
suc n = init (sucT , n , refl)

VecR : (A : Set) → Data
VecR A = (ℕ tt) , VecE
  , End zero
  , Arg (ℕ tt) (λ n → Arg A λ _ → Rec n (End (suc n)))
  , tt

nilD : (A : Set) → Desc (ℕ tt)
nilD A = End zero

consD : (A : Set) → Desc (ℕ tt)
consD A = Arg (ℕ tt) (λ n → Arg A (λ _ → Rec n (End (suc n))))

VecD : (A : Set) → Desc (ℕ tt)
VecD A = DataD (VecR A)

Vec : (A : Set) → ℕ tt → Set
Vec A = μ (VecD A)

NilEl : (A : Set) (n : ℕ tt) → Set
NilEl A n = El (nilD A) (Vec A) n

ConsEl : (A : Set) → ℕ tt → Set
ConsEl A n = El (consD A) (Vec A) n

VecEl : (A : Set) → ℕ tt → Set
VecEl A n = El (VecD A) (Vec A) n

NilHyps : (A : Set) (P : (n : ℕ tt) → Vec A n → Set) (n : ℕ tt) (xs : NilEl A n) → Set
NilHyps A P n xs = Hyps (nilD A) (Vec A) P n xs

ConsHyps : (A : Set) (P : (n : ℕ tt) → Vec A n → Set) (n : ℕ tt) (xs : ConsEl A n) → Set
ConsHyps A P n xs = Hyps (consD A) (Vec A) P n xs

VecHyps : (A : Set) (P : (n : ℕ tt) → Vec A n → Set) (n : ℕ tt) (xs : VecEl A n) → Set
VecHyps A P n xs = Hyps (VecD A) (Vec A) P n xs

ConsUncurriedHyps : (A : Set)
  (P : (n : ℕ tt) → Vec A n → Set)
  (cn : UncurriedEl (consD A) (Vec A)) → Set
ConsUncurriedHyps A P cn = UncurriedHyps (consD A) (Vec A) P cn

nil : (A : Set) → Vec A zero
nil A = init (nilT , refl)

cons : (A : Set) (n : ℕ tt) (x : A) (xs : Vec A n) → Vec A (suc n)
cons A n x xs = init (consT , n , x , xs , refl)

nil2 : (A : Set) → Vec A zero
nil2 A = inj (VecR A) nilT

cons2 : (A : Set) (n : ℕ tt) (x : A) (xs : Vec A n) → Vec A (suc n)
cons2 A = inj (VecR A) consT

----------------------------------------------------------------------

module GenericElim where

  add : ℕ tt → ℕ tt → ℕ tt
  add = elim ℕR _
    (λ n → n)
    (λ m ih n → suc (ih n))
    tt

  mult : ℕ tt → ℕ tt → ℕ tt
  mult = elim ℕR _
    (λ n → zero)
    (λ m ih n → add n (ih n))
    tt

  append : (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)
  append A = elim (VecR A) (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n))
    (λ n ys → ys)
    (λ m x xs ih n ys → cons A (add m n) x (ih n ys))

  concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Vec A (mult n m)
  concat A m = elim (VecR (Vec A m)) (λ n xss → Vec A (mult n m))
    (nil A)
    (λ n xs xss ih → append A m xs (mult n m) ih)

----------------------------------------------------------------------
