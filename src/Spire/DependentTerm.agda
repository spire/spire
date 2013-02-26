module DependentTerm where

----------------------------------------------------------------------

data Context : Set
data Type : Context → Set
data NType : Context → Set
data Val : (Γ : Context) → Type Γ → Set
data NVal : (Γ : Context) → Type Γ → Set
data Var : (Γ : Context) → Type Γ → Set

----------------------------------------------------------------------

infixl 3 _,_
data Context where
  ∅ : Context
  _,_ : (Γ : Context) (A : Type Γ) → Context

----------------------------------------------------------------------

data Type where
  `wkn : ∀{Γ A} → Type Γ → Type (Γ , A)
  `⊤ `Bool : ∀{Γ} → Type Γ
  `neutral : ∀{Γ} → NType Γ → Type Γ

----------------------------------------------------------------------

data NType where
  `if_then_else_ : ∀{Γ} → NVal Γ `Bool
    → Type Γ → Type Γ → NType Γ

----------------------------------------------------------------------

data Val where
  `tt : ∀{Γ} → Val Γ `⊤
  `true `false : ∀{Γ} → Val Γ `Bool
  `neutral : ∀{Γ A} → NVal Γ A → Val Γ A

----------------------------------------------------------------------

data NVal where
  `var : ∀{Γ A} → Var Γ A → NVal Γ A
  `not : ∀{Γ} → NVal Γ `Bool → NVal Γ `Bool

----------------------------------------------------------------------

data Var where
  here : ∀{Γ A} → Var (Γ , A) (`wkn A)
  there : ∀{Γ A B} → Var Γ A → Var (Γ , B) (`wkn A)

----------------------------------------------------------------------

strC : ∀{Γ A} → Var Γ A → Context
strC (here {Γ}) = Γ
strC (there i) = strC i

strT : ∀{Γ A} (i : Var Γ A) → Type (strC i)
strT (here {Γ} {A}) = A
strT (there i) = strT i

Sub : ∀{Γ A} → Var Γ A → Set
Sub i = Val (strC i) (strT i)

----------------------------------------------------------------------

if_then_else_ : ∀{Γ} → Val Γ `Bool → Type Γ → Type Γ → Type Γ
if `true then A else B = A
if `false then A else B = B
if `neutral b then A else B = `neutral (`if b then A else B)

not : ∀{Γ} → Val Γ `Bool → Val Γ `Bool
not `true = `false
not `false = `true
not (`neutral b) = `neutral (`not b)

subC : ∀{Γ A} (i : Var Γ A) → Sub i → Context
subT : ∀{Γ A} → Type Γ → (i : Var Γ A) (x : Sub i) → Type (subC i x)
subNT : ∀{Γ A} → NType Γ → (i : Var Γ A) (x : Sub i) → Type (subC i x)
subV : ∀{Γ A B} → Val Γ B → (i : Var Γ A) (x : Sub i) → Val (subC i x) (subT B i x)
subNV : ∀{Γ A B} → NVal Γ B → (i : Var Γ A) (x : Sub i) → Val (subC i x) (subT B i x)

subC (here {Γ}) x = Γ
subC (there {Γ} {A} {B} i) x = subC i x , subT B i x

subT (`wkn B) i x = {!!}
subT `⊤ i x = `⊤
subT `Bool i x = `Bool
subT (`neutral n) i x = subNT n i x

postulate
  wknVal : ∀{Γ A} (i : Var Γ A) (x : Sub i) → Val (subC i x) (subT A i x)

wknVar : ∀{Γ A B} (i : Var Γ A) (x : Sub i) → Var (subC i x) (subT B i x) → Var Γ B
wknVar i x j = {!!}

data Compare {Γ} {A : Type Γ} (i : Var Γ A) : {B : Type Γ} → Var Γ B → Sub i → Set where
  equal : (x : Val (strC i) (strT i)) → Compare i i x
  diff : ∀{B}
    (x : Val (strC i) (strT i))
    (j : Var (subC i x) (subT B i x))
    → Compare i {B = B} (wknVar i x j) x

postulate
  compare : ∀{Γ A B} (i : Var Γ A) (j : Var Γ B) (x : Sub i) → Compare i j x

subNT (`if b then A else B) i x = if (subNV b i x) then subT A i x else subT B i x

subV `tt i x = `tt
subV `true i x = `true
subV `false i x = `false
subV (`neutral n) i x = subNV n i x

subNV (`var j) i x = {!!}
-- with compare i j x
-- subNV (`var .i) i .x | equal x = wknVal i x
-- subNV (`var .(wknVar i x j)) i .x | diff x j = `neutral (`var j)
subNV (`not b) i x = not (subNV b i x)

----------------------------------------------------------------------

