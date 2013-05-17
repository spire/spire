module Spire.OperationalTypeAndOperationalTerm where

----------------------------------------------------------------------

data Level : Set where
  zero : Level
  suc : Level → Level

----------------------------------------------------------------------

data Context : Set
data Type (Γ : Context) : Set
data Value (Γ : Context) : Type Γ → Set
data Neutral (Γ : Context) : Type Γ → Set

----------------------------------------------------------------------

data Context where
  ∅ : Context
  _,_ : (Γ : Context) → Type Γ → Context

data Type Γ where
  `⊥ `⊤ `Bool : Type Γ
  `Type : (ℓ : Level) → Type Γ
  `Π `Σ : (A : Type Γ) (B : Type (Γ , A)) → Type Γ
  `⟦_⟧ : ∀{ℓ} → Neutral Γ (`Type ℓ) → Type Γ

----------------------------------------------------------------------

⟦_⟧ : ∀{Γ ℓ} → Value Γ (`Type ℓ) →  Type Γ

postulate
  Var : (Γ : Context) (A : Type Γ) → Set
  subT : ∀{Γ A} → Type (Γ , A) → Value Γ A → Type Γ
  subV : ∀{Γ A B} → Value (Γ , A) B → (x : Value Γ A) → Value Γ (subT B x)

----------------------------------------------------------------------

data Value Γ where
  {- Type introduction -}
  `⊥ `⊤ `Bool `Type : ∀{ℓ} → Value Γ (`Type ℓ)
  `Π `Σ : ∀{ℓ} (A : Value Γ (`Type ℓ)) (B : Value (Γ , ⟦ A ⟧) (`Type ℓ)) → Value Γ (`Type ℓ)
  `⟦_⟧ : ∀{ℓ} → Value Γ (`Type ℓ) → Value Γ (`Type (suc ℓ))

  {- Value introduction -}
  `tt : Value Γ `⊤
  `true `false : Value Γ `Bool
  _`,_ : ∀{A B} (a : Value Γ A) (b : Value Γ (subT B a)) → Value Γ (`Σ A B)
  `λ : ∀{A B} → Value (Γ , A) B → Value Γ (`Π A B)
  `neut : ∀{A} → Neutral Γ A → Value Γ A

----------------------------------------------------------------------

data Neutral Γ where
  {- Value elimination -}
  `var : ∀{A} → Var Γ A → Neutral Γ A
  `if_`then_`else_ : ∀{C} (b : Neutral Γ `Bool) (c₁ c₂ : Value Γ C) → Neutral Γ C
  `proj₁ : ∀{A B} → Neutral Γ (`Σ A B) → Neutral Γ A
  `proj₂ : ∀{A B} (ab : Neutral Γ (`Σ A B)) → Neutral Γ (subT B (`neut (`proj₁ ab)))
  _`$_ : ∀{A B} (f : Neutral Γ (`Π A B)) (a : Value Γ A) → Neutral Γ (subT B a)

----------------------------------------------------------------------

⟦ `Π A B ⟧ = `Π ⟦ A ⟧ ⟦ B ⟧
⟦ `Σ A B ⟧ = `Σ ⟦ A ⟧ ⟦ B ⟧
⟦ `⊥ ⟧ = `⊥
⟦ `⊤ ⟧ = `⊤
⟦ `Bool ⟧ = `Bool
⟦ `Type {zero} ⟧ = `⊥
⟦ `Type {suc ℓ} ⟧ = `Type ℓ
⟦ `⟦ A ⟧ ⟧ = ⟦ A ⟧
⟦ `neut A ⟧ = `⟦ A ⟧

----------------------------------------------------------------------

if_then_else_ : ∀{Γ C} (b : Value Γ `Bool) (c₁ c₂ : Value Γ C) → Value Γ C
if `true then c₁ else c₂ = c₁
if `false then c₁ else c₂ = c₂
if `neut b then c₁ else c₂ = `neut (`if b `then c₁ `else c₂)

----------------------------------------------------------------------

proj₁ : ∀{Γ A B} → Value Γ (`Σ A B) → Value Γ A
proj₁ (a `, b) = a
proj₁ (`neut ab) = `neut (`proj₁ ab)

proj₂ : ∀{Γ A B} (ab : Value Γ (`Σ A B)) → Value Γ (subT B (proj₁ ab))
proj₂ (a `, b) = b
proj₂ (`neut ab) = `neut (`proj₂ ab)

----------------------------------------------------------------------

_$_ : ∀{Γ A B} → Value Γ (`Π A B) → (a : Value Γ A) → Value Γ (subT B a)
`λ b $ a = subV b a
`neut f $ a = `neut (f `$ a)

----------------------------------------------------------------------

data Term (Γ : Context) : Type Γ → Set
eval : ∀{Γ A} → Term Γ A → Value Γ A

data Term Γ where
  {- Type introduction -}
  `⊥ `⊤ `Bool `Type : ∀{ℓ} → Term Γ (`Type ℓ)
  `Π `Σ : ∀{ℓ} (A : Term Γ (`Type ℓ)) (B : Term (Γ , ⟦ eval A ⟧) (`Type ℓ)) → Term Γ (`Type ℓ)
  `⟦_⟧ : ∀{ℓ} → Term Γ (`Type ℓ) → Term Γ (`Type (suc ℓ))

  {- Value introduction -}
  `tt : Term Γ `⊤
  `true `false : Term Γ `Bool
  _`,_ : ∀{A B}
    (a : Term Γ A) (b : Term Γ (subT B (eval a)))
    → Term Γ (`Σ A B)
  
  {- Value elimination -}
  `var : ∀{A} → Var Γ A → Term Γ A
  `if_`then_`else_ : ∀{C}
    (b : Term Γ `Bool)
    (c₁ c₂ : Term Γ C)
    → Term Γ C
  _`$_ : ∀{A B} (f : Term Γ (`Π A B)) (a : Term Γ A) → Term Γ (subT B (eval a))
  `proj₁ : ∀{A B} → Term Γ (`Σ A B) → Term Γ A
  `proj₂ : ∀{A B} (ab : Term Γ (`Σ A B)) → Term Γ (subT B (proj₁ (eval ab)))

----------------------------------------------------------------------

{- Type introduction -}
eval `⊥ = `⊥
eval `⊤ = `⊤
eval `Bool = `Bool
eval `Type = `Type
eval (`Π A B) = `Π (eval A) (eval B)
eval (`Σ A B) = `Σ (eval A) (eval B)
eval `⟦ A ⟧ = `⟦ eval A ⟧

{- Value introduction -}
eval `tt = `tt
eval `true = `true
eval `false = `false
eval (a `, b) = eval a `, eval b

{- Value elimination -}
eval (`var i) = `neut (`var i)
eval (`if b `then c₁ `else c₂) = if eval b then eval c₁ else eval c₂
eval (f `$ a) = eval f $ eval a
eval (`proj₁ ab) = proj₁ (eval ab)
eval (`proj₂ ab) = proj₂ (eval ab)

----------------------------------------------------------------------

