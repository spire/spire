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

BranchesD : (I : Set) (E : Enum) → Set
BranchesD I E = Branches E (λ _ → Desc I)

caseD : {I : Set} {E : Enum} (cs : BranchesD I E) (t : Tag E) → Desc I
caseD = case (λ _ → Desc _)

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

data μ {I : Set} (E : Enum) (C : Tag E → Desc I) : ISet I where
  init : (t : Tag E) → UncurriedEl (C t) (μ E C)

inj : {I : Set} (E : Enum) (C : Tag E → Desc I) (t : Tag E) → CurriedEl (C t) (μ E C)
inj E C t = curryEl (C t) (μ E C) (init t)

----------------------------------------------------------------------

hyps : {I : Set} (D : Desc I) (X : I → Set)
  (P : (i : I) → X i → Set)
  (α : (i : I) (x : X i) → P i x)
  (i : I) (xs : El D X i) → Hyps D X P i xs
hyps (End j) X P α i xs = tt
hyps (Rec j D) X P α i x,xs = α j (proj₁ x,xs) , hyps D X P α i (proj₂ x,xs)
hyps (Arg A B) X P α i a,xs = hyps (B (proj₁ a,xs)) X P α i (proj₂ a,xs)

{-# NO_TERMINATION_CHECK #-}
ind : {I : Set} (E : Enum) (C : Tag E → Desc I)
  (P : (i : I) → μ E C i → Set)
  (α : (t : Tag E) → UncurriedHyps (C t) (μ E C) P (init t))
  (i : I)
  (x : μ E C i)
  → P i x
ind E C P α i (init t xs) = α t i xs $
  hyps (C t) (μ E C) P (ind E C P α) i xs

----------------------------------------------------------------------

indCurried : {I : Set} (E : Enum) (C : Tag E → Desc I)
  (P : (i : I) → μ E C i → Set)
  (f : (t : Tag E) → CurriedHyps (C t) (μ E C) P (init t))
  (i : I)
  (x : μ E C i)
  → P i x
indCurried E C P f i x = ind E C P (λ t → uncurryHyps (C t) (μ E C) P (init t) (f t)) i x

Summer : {I : Set} (E : Enum) (C : Tag E → Desc I)
  (X  : ISet I) (cn : (t : Tag E) → UncurriedEl (C t) X)
  (P : (i : I) → X i → Set)
  → Tag E → Set
Summer E C X cn P t = CurriedHyps (C t) X P (cn t)

SumCurriedHyps : {I : Set} (E : Enum) (C : Tag E → Desc I)
  (P : (i : I) → μ E C i → Set)
  → Tag E → Set
SumCurriedHyps E C P t = Summer E C (μ E C) init P t

elimUncurried : {I : Set} (E : Enum) (C : Tag E → Desc I)
  (P : (i : I) → μ E C i → Set)
  → Branches E (SumCurriedHyps E C P)
  → (i : I) (x : μ E C i) → P i x
elimUncurried E C P cs i x =
  indCurried E C P
    (case (SumCurriedHyps E C P) cs)
    i x

elim : {I : Set} (E : Enum) (C : Tag E → Desc I)
  (P : (i : I) → μ E C i → Set)
  → CurriedBranches E
      (SumCurriedHyps E C P)
      ((i : I) (x : μ E C i) → P i x)
elim E C P = curryBranches (elimUncurried E C P)

----------------------------------------------------------------------

Soundness : Set₁
Soundness = {I : Set} (E : Enum) (C : Tag E → Desc I)
  (P : (i : I) → μ E C i → Set)
  (cs : Branches E (SumCurriedHyps E C P))
  (i : I) (x : μ E C i)
  → ∃ λ α
  → elimUncurried E C P cs i x ≡ ind E C P α i x

sound : Soundness
sound E C P cs i xs =
  let D = Arg (Tag E) C in
  (λ t → uncurryHyps (C t) (μ E C) P (init t) (case (SumCurriedHyps E C P) cs t)) , refl

Completeness : Set₁
Completeness = {I : Set} (E : Enum) (C : Tag E → Desc I)
  (P : (i : I) → μ E C i → Set)
  (α : (t : Tag E) → UncurriedHyps (C t) (μ E C) P (init t))
  (i : I) (x : μ E C i)
  → ∃ λ cs
  → ind E C P α i x ≡ elimUncurried E C P cs i x

uncurryHypsIdent : {I : Set} (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedEl D X)
  (α : UncurriedHyps D X P cn)
  (i : I) (xs : El D X i) (ihs : Hyps D X P i xs)
  → α i xs ihs ≡ uncurryHyps D X P cn (curryHyps D X P cn α) i xs ihs
uncurryHypsIdent (End .i) X P cn α i refl tt = refl
uncurryHypsIdent (Rec j D) X P cn α i (x , xs) (p , ps) =
  uncurryHypsIdent D X P (λ xs → cn (x , xs)) (λ k ys rs → α k (x , ys) (p , rs)) i xs ps
uncurryHypsIdent (Arg A B) X P cn α i (a , xs) ps =
  uncurryHypsIdent (B a) X P (λ xs → cn (a , xs)) (λ j ys → α j (a , ys)) i xs ps

postulate
  ext4 : {A : Set} {B : A → Set} {C : (a : A) → B a → Set}
    {D : (a : A) (b : B a) → C a b → Set}
    {Z : (a : A) (b : B a) (c : C a b) → D a b c → Set}
    (f g : (a : A) (b : B a) (c : C a b) (d : D a b c) → Z a b c d)
    → ((a : A) (b : B a) (c : C a b) (d : D a b c) → f a b c d ≡ g a b c d)
    → f ≡ g

toBranches : {I : Set} (E : Enum) (C : Tag E → Desc I)
  (X  : ISet I) (cn : (t : Tag E) → UncurriedEl (C t) X)
  (P : (i : I) → X i → Set)
  (α : (t : Tag E) → UncurriedHyps (C t) X P (cn t))
  → Branches E (Summer E C X cn P)
toBranches [] C X cn P α = tt
toBranches (l ∷ E) C X cn P α =
    curryHyps (C here) X P (λ xs → cn here xs) (λ i xs → α here i xs)
  , toBranches E (λ t → C (there t)) X
     (λ t → cn (there t))
     P (λ t i xs ih → α (there t) i xs ih)

ToBranches : {I : Set} {E : Enum} (C : Tag E → Desc I)
  (X  : ISet I) (cn : (t : Tag E) → UncurriedEl (C t) X)
  (P : (i : I) → X i → Set)
  (α : (t : Tag E) → UncurriedHyps (C t) X P (cn t))
  (t : Tag E)
  → let β = toBranches E C X cn P α in
  case (Summer E C X cn P) β t ≡ curryHyps (C t) X P (cn t) (α t)
ToBranches C X cn P α here = refl
ToBranches C X cn P α (there t)
  with ToBranches (λ t → C (there t)) X
    (λ t xs → cn (there t) xs)
    P (λ t i xs ih → α (there t) i xs ih) t
... | ih rewrite ih = refl

completeα : {I : Set} (E : Enum) (C : Tag E → Desc I)
  (P : (i : I) → μ E C i → Set)
  (α : (t : Tag E) → UncurriedHyps (C t) (μ E C) P (init t))
  (t : Tag E) (i : I) (xs : El (C t) (μ E C) i) (ihs : Hyps (C t) (μ E C) P i xs)
  → let β = toBranches E C (μ E C) init P α in
  α t i xs ihs ≡ uncurryHyps (C t) (μ E C) P (init t) (case (SumCurriedHyps E C P) β t) i xs ihs
completeα E C P α t i xs ihs
  with ToBranches C (μ E C) init P α t
... | q rewrite q = uncurryHypsIdent (C t) (μ E C) P (init t) (α t) i xs ihs

complete' : {I : Set} (E : Enum) (C : Tag E → Desc I)
  (P : (i : I) → μ E C i → Set)
  (α : (t : Tag E) → UncurriedHyps (C t) (μ E C) P (init t))
  (i : I) (x : μ E C i)
  → let β = toBranches E C (μ E C) init P α in
  ind E C P α i x ≡ elimUncurried E C P β i x
complete' E C P α i (init t xs) = cong
  (λ f → ind E C P f i (init t xs))
  (ext4 α
    (λ t → uncurryHyps (C t) (μ E C) P (init t) (case (SumCurriedHyps E C P) β t))
    (completeα E C P α)
  )
  where β = toBranches E C (μ E C) init P α

complete : Completeness
complete E C P α i x =
  let D = Arg (Tag E) C in
    toBranches E C (μ E C) init P α
  , complete' E C P α i x

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

ℕC : ℕT → Desc ⊤
ℕC = caseD $
    End tt
  , Rec tt (End tt)
  , tt

ℕD : Desc ⊤
ℕD = Arg ℕT ℕC

ℕ : ⊤ → Set
ℕ = μ ℕE ℕC

zero : ℕ tt
zero = init zeroT refl

suc : ℕ tt → ℕ tt
suc n = init sucT (n , refl)

VecC : (A : Set) → VecT → Desc (ℕ tt)
VecC A = caseD $
    End zero
  , Arg (ℕ tt) (λ n → Arg A λ _ → Rec n (End (suc n)))
  , tt

nilD : (A : Set) → Desc (ℕ tt)
nilD A = End zero

consD : (A : Set) → Desc (ℕ tt)
consD A = Arg (ℕ tt) (λ n → Arg A (λ _ → Rec n (End (suc n))))

VecD : (A : Set) → Desc (ℕ tt)
VecD A = Arg VecT (VecC A)

Vec : (A : Set) → ℕ tt → Set
Vec A = μ VecE (VecC A)

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
nil A = init nilT refl

cons : (A : Set) (n : ℕ tt) (x : A) (xs : Vec A n) → Vec A (suc n)
cons A n x xs = init consT (n , x , xs , refl)

nil2 : (A : Set) → Vec A zero
nil2 A = inj VecE (VecC A) nilT

cons2 : (A : Set) (n : ℕ tt) (x : A) (xs : Vec A n) → Vec A (suc n)
cons2 A = inj VecE (VecC A) consT

----------------------------------------------------------------------

module Induction where

  add : ℕ tt → ℕ tt → ℕ tt
  add = ind ℕE ℕC _
    (case (λ t → UncurriedHyps (ℕC t) ℕ _ (init t))
      ( (λ u q ih n → n)
      , (λ u m,q ih,tt n → suc (proj₁ ih,tt n))
      , tt
      )
    )
    tt
  
  mult : ℕ tt → ℕ tt → ℕ tt
  mult = ind ℕE ℕC _
    (case (λ t → UncurriedHyps (ℕC t) ℕ _ (init t))
      ( (λ u q ih n → zero)
      , (λ u m,q ih,tt n → add n (proj₁ ih,tt n))
      , tt
      )
    )
    tt
  
  append : (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n) 
  append A = ind VecE (VecC A) _
    (case (λ t → UncurriedHyps (VecC A t) (Vec A) _ (init t))
      ( (λ m q ih n ys → subst (λ m → Vec A (add m n)) q ys)
      , (λ m m',x,xs,q ih,tt n ys →
          let m' = proj₁ m',x,xs,q
              x = proj₁ (proj₂ m',x,xs,q)
              q = proj₂ (proj₂ (proj₂ m',x,xs,q))
              ih = proj₁ ih,tt
          in
          subst (λ m → Vec A (add m n)) q (cons A (add m' n) x (ih n ys))
        )
      , tt
      )
    )

  concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Vec A (mult n m)
  concat A m = ind VecE (VecC (Vec A m)) _
    (case (λ t → UncurriedHyps (VecC (Vec A m) t) (Vec (Vec A m)) _ (init t))
      ( (λ n q ih → subst (λ n → Vec A (mult n m)) q (nil A))
      , (λ n n',x,xs,q ih,tt →
          let n' = proj₁ n',x,xs,q
              xs = proj₁ (proj₂ n',x,xs,q)
              q = proj₂ (proj₂ (proj₂ n',x,xs,q))
              ih = proj₁ ih,tt
          in subst  (λ n → Vec A (mult n m)) q (append A m xs (mult n' m) ih)
        )
      , tt
      )
    )

----------------------------------------------------------------------

module GenericElim where

  add : ℕ tt → ℕ tt → ℕ tt
  add = elim ℕE ℕC _
    (λ n → n)
    (λ m ih n → suc (ih n))
    tt

  mult : ℕ tt → ℕ tt → ℕ tt
  mult = elim ℕE ℕC _
    (λ n → zero)
    (λ m ih n → add n (ih n))
    tt

  append : (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)
  append A = elim VecE (VecC A) (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n))
    (λ n ys → ys)
    (λ m x xs ih n ys → cons A (add m n) x (ih n ys))

  concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Vec A (mult n m)
  concat A m = elim VecE (VecC (Vec A m)) (λ n xss → Vec A (mult n m))
    (nil A)
    (λ n xs xss ih → append A m xs (mult n m) ih)

----------------------------------------------------------------------
