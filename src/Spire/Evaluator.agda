module Spire.Evaluator where

----------------------------------------------------------------------

data Con : Set
data Type : Con → Set
data NType : Con → Set
data Val : (Γ : Con) → Type Γ → Set
data NVal : (Γ : Con) → Type Γ → Set
data Var : (Γ : Con) → Type Γ → Set
strC : ∀{Γ A} → Var Γ A → Con
strT : ∀{Γ A} (i : Var Γ A) → Type (strC i)
Sub : ∀{Γ A} → Var Γ A → Set
subC : ∀{Γ A} (i : Var Γ A) → Sub i → Con
subT : ∀{Γ A} → Type Γ → (i : Var Γ A) (x : Sub i) → Type (subC i x)
subNT : ∀{Γ A} → NType Γ → (i : Var Γ A) (x : Sub i) → Type (subC i x)
subV : ∀{Γ A B} → Val Γ B → (i : Var Γ A) (x : Sub i) → Val (subC i x) (subT B i x)
subNV : ∀{Γ A B} → NVal Γ B → (i : Var Γ A) (x : Sub i) → Val (subC i x) (subT B i x)

----------------------------------------------------------------------

infixl 3 _,_
data Con where
  ∅ : Con
  _,_ : (Γ : Con) (A : Type Γ) → Con

data Type where
  `wkn : ∀{Γ A} → Type Γ → Type (Γ , A)
  `⊤ `Bool : ∀{Γ} → Type Γ
  _`→_ : ∀{Γ} (A B : Type Γ) → Type Γ
  `neutral : ∀{Γ} → NType Γ → Type Γ

data NType where
  `if_then_else_ : ∀{Γ} → NVal Γ `Bool
    → Type Γ → Type Γ → NType Γ

----------------------------------------------------------------------

data Val where
  `wkn : ∀{Γ A B} → Val Γ A → Val (Γ , B) (`wkn A)
  `tt : ∀{Γ} → Val Γ `⊤
  `true `false : ∀{Γ} → Val Γ `Bool
  `λ : ∀{Γ A B} → Val (Γ , A) (`wkn B) → Val Γ (A `→ B)
  `neutral : ∀{Γ A} → NVal Γ A → Val Γ A

data NVal where
  `var : ∀{Γ A} → Var Γ A → NVal Γ A
  `not : ∀{Γ} → NVal Γ `Bool → NVal Γ `Bool
  _`$_ : ∀{Γ A B} → NVal Γ (A `→ B) → Val Γ A → NVal Γ B

data Var where
  here : ∀{Γ A} → Var (Γ , A) (`wkn A)
  there : ∀{Γ A B} (i : Var Γ A) → Var (Γ , B) (`wkn A)

----------------------------------------------------------------------

if_then_else_ : ∀{Γ} → Val Γ `Bool → Type Γ → Type Γ → Type Γ
if `true then A else B = A
if `false then A else B = B
if `neutral b then A else B = `neutral (`if b then A else B)

not : ∀{Γ} → Val Γ `Bool → Val Γ `Bool
not `true = `false
not `false = `true
not (`neutral b) = `neutral (`not b)

_$_ : ∀{Γ A B} → Val Γ (A `→ B) → Val Γ A → Val Γ B

----------------------------------------------------------------------

strC (here {Γ}) = Γ
strC (there i) = strC i
strT (here {Γ} {A}) = A
strT (there i) = strT i
Sub i = Val (strC i) (strT i)
subC (here {Γ}) x = Γ
subC (there {Γ} {A} {B} i) x = subC i x , subT B i x
subT (`wkn A) here x = A
subT (`wkn A) (there i) x = `wkn (subT A i x)
subT `⊤ i x = `⊤
subT `Bool i x = `Bool
subT (A `→ B) i x = subT A i x `→ subT B i x
subT (`neutral n) i x = subNT n i x
subNT (`if b then A else B) i x = if (subNV b i x) then subT A i x else subT B i x
subV (`wkn a) here x = a
subV (`wkn a) (there i) x = `wkn (subV a i x)
subV `tt i x = `tt
subV `true i x = `true
subV `false i x = `false
subV (`λ f) i x = `λ (subV f (there i) x)
subV (`neutral n) i x = subNV n i x
{-# NO_TERMINATION_CHECK #-}
subNV (`var here) here x = x
subNV (`var here) (there i) x = `neutral (`var here)
subNV (`var (there j)) here x = `neutral (`var j)
subNV (`var (there j)) (there i) x = `wkn (subNV (`var j) i x)
subNV (`not b) i x = not (subNV b i x)
subNV (f `$ a) i x = subNV f i x $ (subV a i x)

`λ f $ a = subV f here a
`neutral f $ a = `neutral (f `$ a)

----------------------------------------------------------------------

data TermType : (Γ : Con) → Set
data Term : (Γ : Con) → Type Γ → Set

data TermType where
  `wkn : ∀{Γ A} → TermType Γ → TermType (Γ , A)
  `⊤ `Bool : ∀{Γ} → TermType Γ
  _`→_ : ∀{Γ} (A B : TermType Γ) → TermType Γ
  `if_then_else_ : ∀{Γ}
    → Term Γ `Bool
    → TermType Γ → TermType Γ
    → TermType Γ

data Term where
  `wkn : ∀{Γ A B} → Term Γ B → Term (Γ , A) (`wkn B)
  `var : ∀{Γ A} (i : Var Γ A) → Term Γ A
  `tt : ∀{Γ} → Term Γ `⊤
  `true `false : ∀{Γ} → Term Γ `Bool
  `λ : ∀{Γ A B} → Term (Γ , A) (`wkn B) → Term Γ (A `→ B)
  `not : ∀{Γ} (b : Term Γ `Bool) → Term Γ `Bool
  _`$_ : ∀{Γ A B}
    → Term Γ (A `→ B)
    → Term Γ A
    → Term Γ B

evalType : ∀{Γ} → TermType Γ → Type Γ
eval : ∀{Γ A} → Term Γ A → Val Γ A

evalType (`wkn A) = `wkn (evalType A)
evalType `⊤ = `⊤
evalType `Bool = `Bool
evalType (A `→ B) = evalType A `→ evalType B
evalType (`if b then A else B) = if eval b then evalType A else evalType B
eval (`wkn a) = `wkn (eval a)
eval (`var i) = `neutral (`var i)
eval `tt = `tt
eval `true = `true
eval `false = `false
eval (`λ f) = `λ (eval f)
eval (`not b) = not (eval b)
eval (f `$ a) = eval f $ eval a

----------------------------------------------------------------------

embV : ∀{Γ A} → Val Γ A → Term Γ A
embNV : ∀{Γ A} → NVal Γ A → Term Γ A
embT : ∀{Γ} → Type Γ → TermType Γ
embNT : ∀{Γ} → NType Γ → TermType Γ

embV (`wkn A) = `wkn (embV A)
embV `tt = `tt
embV `true = `true
embV `false = `false
embV (`λ f) = `λ (embV f)
embV (`neutral a) = embNV a
embNV (`var i) = `var i
embNV (`not b) = `not (embNV b)
embNV (f `$ a) = embNV f `$ embV a
embT (`wkn A) = `wkn (embT A)
embT `⊤ = `⊤
embT `Bool = `Bool
embT (A `→ B) = embT A `→ embT B
embT (`neutral A) = embNT A
embNT (`if b then A else B) = `if embNV b then embT A else embT B

----------------------------------------------------------------------
