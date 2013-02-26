module Spire.Term where
{-# IMPORT Spire.SurfaceTerm #-}

----------------------------------------------------------------------

data Type : Set where
  `⊤ `Bool : Type
{-# COMPILED_DATA Type Spire.SurfaceTerm.Type
  Spire.SurfaceTerm.Unit Spire.SurfaceTerm.Bool
#-}

infixl 3 _,_
data Con : Set where
  ∅ : Con
  _,_ : Con → Type → Con

data Var : Con → Type → Set where
  here : ∀{Γ A} → Var (Γ , A) A
  there : ∀{Γ A B} → Var Γ A → Var (Γ , B) A

_-_ : ∀{A} (Γ : Con) → Var Γ A → Con
∅ - ()
(Γ , A) - here = Γ
(Γ , A) - there i = Γ - i , A

wknV : ∀{Γ A B} (i : Var Γ A) → Var (Γ - i) B → Var Γ B
wknV here j = there j
wknV (there i) here = here
wknV (there i) (there j) = there (wknV i j)

data Compare {Γ A} (i : Var Γ A) : {B : Type} → Var Γ B → Set where
  equal : Compare i i
  diff : ∀{B} (j : Var (Γ - i) B) → Compare i (wknV i j)

compare : ∀{Γ A B} (i : Var Γ A) (j : Var Γ B) → Compare i j
compare here here = equal
compare here (there j) = diff j
compare (there i) here = diff here
compare (there i) (there j) with compare i j
compare (there i) (there .i) | equal = equal
compare (there i) (there .(wknV i j)) | diff j = diff (there j)

----------------------------------------------------------------------

data Val : Con → Type → Set
data NVal : Con → Type → Set

data Val where
  `tt : ∀{Γ} → Val Γ `⊤
  `true `false : ∀{Γ} → Val Γ `Bool
  `neutral : ∀{Γ A} → NVal Γ A → Val Γ A

data NVal where
  `var : ∀{Γ A} → Var Γ A → NVal Γ A
  `if_then_else_ : ∀{Γ C}
    (b : NVal Γ `Bool) (c₁ c₂ : Val Γ C)
    → NVal Γ C

----------------------------------------------------------------------

if_then_else_ : ∀{Γ C} (b : Val Γ `Bool) (c₁ c₂ : Val Γ C) → Val Γ C
if `true then c₁ else c₂ = c₁
if `false then c₁ else c₂ = c₂
if `neutral n then c₁ else c₂ = `neutral (`if n then c₁ else c₂)

----------------------------------------------------------------------

subV : ∀{Γ A B} → Val Γ B → (i : Var Γ A) → Val (Γ - i) A → Val (Γ - i) B
subNV : ∀{Γ A B} → NVal Γ B → (i : Var Γ A) → Val (Γ - i) A → Val (Γ - i) B

subV `tt i x = `tt
subV `true i x = `true
subV `false i x = `false
subV (`neutral n) i x = subNV n i x

subNV (`var j) i x with compare i j
subNV (`var .i) i x | equal = x
subNV (`var .(wknV i j)) i x | diff j = `neutral (`var j)
subNV (`if b then c₁ else c₂) i x = if subNV b i x then subV c₁ i x else subV c₂ i x

----------------------------------------------------------------------

data Term : Con → Type → Set where
  `var : ∀{Γ A} → Var Γ A → Term Γ A
  `tt : ∀{Γ} → Term Γ `⊤
  `true `false : ∀{Γ} → Term Γ `Bool
  `if_then_else_ : ∀{Γ C}
    (b : Term Γ `Bool) (c₁ c₂ : Term Γ C)
    → Term Γ C

eval : ∀{Γ A} → Term Γ A → Val Γ A
eval (`var i) = `neutral (`var i)
eval `tt = `tt
eval `true = `true
eval `false = `false
eval (`if b then c₁ else c₂) = if eval b then eval c₁ else eval c₂

----------------------------------------------------------------------

embV : ∀{Γ A} → Val Γ A → Term Γ A
embNV : ∀{Γ A} → NVal Γ A → Term Γ A

embV `tt = `tt
embV `true = `true
embV `false = `false
embV (`neutral n) = embNV n

embNV (`var i) = `var i
embNV (`if b then c₁ else c₂) = `if embNV b then embV c₁ else embV c₂

----------------------------------------------------------------------
