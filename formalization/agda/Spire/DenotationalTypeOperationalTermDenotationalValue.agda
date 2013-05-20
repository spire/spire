open import Spire.DenotationalType
module Spire.DenotationalTypeOperationalTermDenotationalValue where

----------------------------------------------------------------------

data Context : Set₁
Environment : Context → Set

ScopedType : Context → Set₁
ScopedType Γ = Environment Γ → Set

data Context where
  ∅ : Context
  _,_ : (Γ : Context) (A : ScopedType Γ) → Context

Environment ∅ = ⊤
Environment (Γ , A) = Σ (Environment Γ) A

data Var :  (Γ : Context) (A : ScopedType Γ) → Set₁ where
 here : ∀{Γ A} → Var (Γ , A) (λ vs → A (proj₁ vs))
 there : ∀{Γ A} {B : ScopedType Γ}
   → Var Γ A → Var (Γ , B) (λ vs → A (proj₁ vs))

lookup : ∀{Γ A} → Var Γ A → (vs : Environment Γ) → A vs
lookup here (vs , v) = v
lookup (there i) (vs , v) = lookup i vs

ScopedType₂ : (Γ : Context) → ScopedType Γ → Set₁
ScopedType₂ Γ A = (vs : Environment Γ) → A vs → Set

----------------------------------------------------------------------

data Term (Γ : Context) : ScopedType Γ → Set₁
eval : ∀{Γ A} → Term Γ A → (vs : Environment Γ) → A vs

-- ----------------------------------------------------------------------

data Term Γ where
  {- Type introduction -}
  `⊥ `⊤ `Bool `ℕ `Type : ∀{ℓ}
    → Term Γ (const (Type ℓ))
  `Π `Σ : ∀{ℓ}
    (A : Term Γ (const (Type ℓ)))
    (B : Term (Γ , λ vs → ⟦ ℓ ∣ eval A vs ⟧) (const (Type ℓ)))
    → Term Γ (λ _ → Type ℓ)
  `⟦_⟧ : ∀{ℓ}
    (A : Term Γ (const (Type ℓ)))
    → Term Γ (const (Type (suc ℓ)))

  {- Value introduction -}
  `tt : Term Γ (const ⊤)
  `true `false : Term Γ (const Bool)
  `zero : Term Γ (const ℕ)
  `suc : Term Γ (const ℕ) → Term Γ (const ℕ)
  `λ : ∀{A} {B : ScopedType₂ Γ A}
    (f : Term (Γ , A) (λ vs → B (proj₁ vs) (proj₂ vs)))
    → Term Γ (λ vs → (v : A vs) → (B vs v))
  _`,_ : ∀{A} {B : ScopedType₂ Γ A}
    (a : Term Γ A)
    (b : Term Γ (λ vs → B vs (eval a vs)))
    → Term Γ (λ vs → Σ (A vs) (λ v → B vs v))

  {- Value elimination -}
  `var : ∀{A} (a : Var Γ A) → Term Γ A
  `elim⊥ : ∀{A ℓ}
    (P : Term Γ (const (Type ℓ)))
    (x : Term Γ (const ⊥))
    → Term Γ A
  `elimBool : ∀{ℓ}
    (P : Term (Γ , const Bool) (const (Type ℓ)))
    (pt : Term Γ (λ vs → ⟦ ℓ ∣ eval P (vs , true) ⟧))
    (pf : Term Γ (λ vs → ⟦ ℓ ∣ eval P (vs , false) ⟧))
    (b : Term Γ (const Bool))
    → Term Γ (λ vs → ⟦ ℓ ∣ eval P (vs , eval b vs) ⟧)
  `elimℕ : ∀{ℓ}
    (P : Term (Γ , (const ℕ)) (const (Type ℓ)))
    (pz : Term Γ (λ vs → ⟦ ℓ ∣ eval P (vs , zero) ⟧))
    (ps : Term ((Γ , const ℕ) , (λ { (vs , n)  → ⟦ ℓ ∣ eval P (vs , n) ⟧ }))
            (λ { ((vs , n) , p) → ⟦ ℓ ∣ eval P (vs , suc n) ⟧ }))
    (n : Term Γ (const ℕ))
    → Term Γ (λ vs → ⟦ ℓ ∣ eval P (vs , eval n vs) ⟧)
  _`$_ : ∀{A} {B : ScopedType₂ Γ A}
    (f : Term Γ (λ vs → (v : A vs) → (B vs v)))
    (a : Term Γ A)
    → Term Γ (λ vs → B vs (eval a vs))
  `proj₁ : ∀{A} {B : ScopedType₂ Γ A}
    (ab : Term Γ (λ vs → Σ (A vs) (B vs)))
    → Term Γ A
  `proj₂ : ∀{A} {B : ScopedType₂ Γ A}
    (ab : Term Γ (λ vs → Σ (A vs) (B vs)))
    → Term Γ (λ vs → B vs (proj₁ (eval ab vs)))

----------------------------------------------------------------------

{- Type introduction -}
eval `⊥ vs = `⊥
eval `⊤ vs = `⊤
eval `Bool vs = `Bool
eval `ℕ vs = `ℕ
eval `Type vs = `Type
eval (`Π A B) vs = `Π (eval A vs) λ v → eval B (vs , v)
eval (`Σ A B) vs = `Σ (eval A vs) λ v → eval B (vs , v)
eval `⟦ A ⟧ vs = `⟦ eval A vs ⟧

{- Value introduction -}
eval `tt vs = tt
eval `true vs = true
eval `false vs = false
eval `zero vs = zero
eval (`suc n) vs = suc (eval n vs)
eval (`λ f) vs = λ v → eval f (vs , v)
eval (a `, b) vs = eval a vs , eval b vs

{- Value elimination -}
eval (`var i) vs = lookup i vs
eval (`elim⊥ P x) vs = elim⊥ (eval x vs)
eval (`elimBool {ℓ} P pt pf b) vs =
  elimBool (λ v → ⟦ ℓ ∣ eval P (vs , v) ⟧)
    (eval pt vs)
    (eval pf vs)
    (eval b vs)
eval (`elimℕ {ℓ} P pz ps n) vs =
  elimℕ (λ v → ⟦ ℓ ∣ eval P (vs , v) ⟧)
    (eval pz vs)
    (λ n rec → eval ps ((vs , n) , rec))
    (eval n vs)
eval (f `$ a) vs = (eval f vs) (eval a vs)
eval (`proj₁ ab) vs = proj₁ (eval ab vs)
eval (`proj₂ ab) vs = proj₂ (eval ab vs)

----------------------------------------------------------------------
