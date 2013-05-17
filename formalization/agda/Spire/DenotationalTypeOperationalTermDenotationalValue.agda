open import Spire.DenotationalType
module Spire.DenotationalTypeOperationalTermDenotationalValue where

----------------------------------------------------------------------

data Context : Set
Environment : Context → Set

ScopedType : Context → ℕ → Set
ScopedType Γ ℓ = Environment Γ → Type ℓ

data Context where
  ∅ : Context
  extend : (Γ : Context) (ℓ : ℕ) (A : ScopedType Γ ℓ) → Context

Environment ∅ = ⊤
Environment (extend Γ ℓ A) = Σ (Environment Γ) (λ vs → ⟦ ℓ ∣ A vs ⟧)

data Var :  (Γ : Context) (ℓ : ℕ) (A : ScopedType Γ ℓ) → Set where
 here : ∀{Γ ℓ A} → Var (extend Γ ℓ A) ℓ (λ vs → A (proj₁ vs))
 there : ∀{Γ ℓ A ℓ′} {B : ScopedType Γ ℓ′}
   → Var Γ ℓ A → Var (extend Γ ℓ′ B) ℓ (λ vs → A (proj₁ vs))

lookup : ∀{Γ ℓ A} → Var Γ ℓ A → (vs : Environment Γ) → ⟦ ℓ ∣ A vs ⟧
lookup here (vs , v) = v
lookup (there i) (vs , v) = lookup i vs

ScopedType₂ : (Γ : Context) (ℓ : ℕ) → ScopedType Γ ℓ → Set
ScopedType₂ Γ ℓ A = (vs : Environment Γ) → ⟦ ℓ ∣ A vs ⟧ → Type ℓ

----------------------------------------------------------------------

data Term (Γ : Context) : (ℓ : ℕ) → ScopedType Γ ℓ → Set
eval : ∀{Γ ℓ A} → Term Γ ℓ A → (vs : Environment Γ) → ⟦ ℓ ∣ A vs ⟧

----------------------------------------------------------------------

data Term Γ where
  {- Type introduction -}
  `⊥ `⊤ `Bool `ℕ `Type : ∀{ℓ}
    → Term Γ (suc ℓ) (const `Type)
  `Π `Σ : ∀{ℓ}
    (A : Term Γ (suc ℓ) (const `Type))
    (B : Term (extend Γ ℓ (eval A))
      (suc ℓ) (const `Type))
    → Term Γ (suc ℓ) (const `Type)
  `⟦_⟧ : ∀{ℓ}
    (A : Term Γ ℓ (const `Type))
    → Term Γ (suc ℓ) (const `Type)

  {- Value introduction -}
  `tt : ∀{ℓ} → Term Γ ℓ (const `⊤)
  `true `false : ∀{ℓ} → Term Γ ℓ (const `Bool)
  `zero : ∀{ℓ} → Term Γ ℓ (const `ℕ)
  `suc : ∀{ℓ} → Term Γ ℓ (const `ℕ)
    → Term Γ ℓ (const `ℕ)
  `λ : ∀{ℓ A} {B : ScopedType₂ Γ ℓ A}
    (f : Term (extend Γ ℓ A) ℓ (uncurry B))
    → Term Γ ℓ λ vs → `Π (A vs) λ v → (B vs v)
  _`,_ : ∀{ℓ A} {B : ScopedType₂ Γ ℓ A}
    (a : Term Γ ℓ A)
    (b : Term Γ ℓ λ vs → B vs (eval a vs))
    → Term Γ ℓ λ vs → `Σ (A vs) λ v → B vs v
  `lift : ∀{ℓ A}
    (a : Term Γ ℓ A)
    → Term Γ (suc ℓ) λ vs → `⟦ A vs ⟧

  {- Value elimination -}
  `var : ∀{ℓ A} (a : Var Γ ℓ A) → Term Γ ℓ A
  `lower : ∀{ℓ A}
    (a : Term Γ (suc ℓ) λ vs → `⟦ A vs ⟧)
    → Term Γ ℓ A
  `case⊥ : ∀{ℓ A}
    (P : Term Γ ℓ (const `Type))
    (x : Term Γ ℓ (const `⊥))
    → Term Γ ℓ A
  `caseBool : ∀{ℓ}
    (P : Term (extend Γ ℓ (const `Bool))
      (suc ℓ) (const `Type))
    (pt : Term Γ ℓ λ vs → eval P (vs , true))
    (pf : Term Γ ℓ λ vs → eval P (vs , false))
    (b : Term Γ ℓ (const `Bool))
    → Term Γ ℓ λ vs → eval P (vs , eval b vs)
  `caseℕ : ∀{ℓ}
    (P : Term (extend Γ ℓ (const `ℕ))
      (suc ℓ) (const `Type))
    (pz : Term Γ ℓ λ vs → eval P (vs , zero))
    (ps : Term (extend (extend Γ ℓ (const `ℕ)) ℓ
            (λ { (vs , n) → eval P (vs , n) })
            ) ℓ
            (λ { ((vs , n) , p) → eval P (vs , suc n) }))
    (n : Term Γ ℓ (const `ℕ))
    → Term Γ ℓ λ vs → eval P (vs , eval n vs)
  _`$_ : ∀{ℓ A} {B : ScopedType₂ Γ ℓ A}
    (f : Term Γ ℓ (λ vs → `Π (A vs) (B vs)))
    (a : Term Γ ℓ A)
    → Term Γ ℓ λ vs → B vs (eval a vs)
  `proj₁ : ∀{ℓ A} {B : ScopedType₂ Γ ℓ A}
    (ab : Term Γ ℓ (λ vs → `Σ (A vs) (B vs)))
    → Term Γ ℓ A
  `proj₂ : ∀{ℓ A} {B : ScopedType₂ Γ ℓ A}
    (ab : Term Γ ℓ (λ vs → `Σ (A vs) (B vs)))
    → Term Γ ℓ λ vs → B vs (proj₁ (eval ab vs))

----------------------------------------------------------------------

{- Type introduction -}
eval `⊥ vs = `⊥
eval `⊤ vs = `⊤
eval `Bool vs = `Bool
eval `ℕ vs = `ℕ
eval (`Π A B) vs = `Π (eval A vs) λ v → eval B (vs , v)
eval (`Σ A B) vs = `Σ (eval A vs) λ v → eval B (vs , v)
eval `Type vs = `Type
eval `⟦ A ⟧ vs = `⟦ eval A vs ⟧

{- Value introduction -}
eval `tt vs = tt
eval `true vs = true
eval `false vs = false
eval `zero vs = zero
eval (`suc n) vs = suc (eval n vs)
eval (`λ f) vs = λ v → eval f (vs , v)
eval (a `, b) vs = eval a vs , eval b vs
eval (`lift a) vs = eval a vs
eval (`var i) vs = lookup i vs

{- Value elimination -}
eval (`lower a) vs = eval a vs
eval (`case⊥ P x) vs = case⊥ (eval x vs)
eval (`caseBool {ℓ} P pt pf b) vs =
  caseBool (λ v → ⟦ ℓ ∣ eval P (vs , v) ⟧)
    (eval pt vs)
    (eval pf vs)
    (eval b vs)
eval (`caseℕ {ℓ} P pz ps n) vs =
  caseℕ (λ v → ⟦ ℓ ∣ eval P (vs , v) ⟧)
    (eval pz vs)
    (λ n rec → eval ps ((vs , n) , rec))
    (eval n vs)
eval (f `$ a) vs = (eval f vs) (eval a vs)
eval (`proj₁ ab) vs = proj₁ (eval ab vs)
eval (`proj₂ ab) vs = proj₂ (eval ab vs)

----------------------------------------------------------------------
