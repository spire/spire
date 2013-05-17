open import Spire.DenotationalType
module Spire.DenotationalTypeDenotationalTermDenotationalValue where

----------------------------------------------------------------------

data Term : ∀ ℓ → Type ℓ → Set
eval : ∀{ℓ} {A : Type ℓ} → Term ℓ A → ⟦ ℓ ∣ A ⟧

----------------------------------------------------------------------

data Term where
  {- Type introduction -}
  `⊥ `⊤ `Bool `ℕ `Type : ∀{ℓ} → Term (suc ℓ) `Type
  `Π `Σ : ∀{ℓ}
    (A : Term (suc ℓ) `Type)
    (B : ⟦ ℓ ∣ eval A ⟧ → Term (suc ℓ) `Type)
    → Term (suc ℓ) `Type
  `⟦_⟧ : ∀{ℓ}
    (A : Term ℓ `Type)
    → Term (suc ℓ) `Type

  {- Value introduction -}
  `tt : ∀{ℓ} → Term ℓ `⊤
  `true `false : ∀{ℓ} → Term ℓ `Bool
  `zero : ∀{ℓ} → Term ℓ `ℕ
  `suc : ∀{ℓ} → Term ℓ `ℕ → Term ℓ `ℕ
  `λ : ∀{ℓ A B}
    (f : (a : ⟦ ℓ ∣ A ⟧) → Term ℓ (B a))
    → Term ℓ (`Π A B)
  _`,_ : ∀{ℓ A B}
    (a : Term ℓ A)
    (b : Term ℓ (B (eval a)))
    → Term ℓ (`Σ A B)
  `lift : ∀{ℓ A}
    (a : Term ℓ A)
    → Term (suc ℓ) `⟦ A ⟧

  {- Value elimination -}
  `lower : ∀{ℓ A}
    (a : Term (suc ℓ) `⟦ A ⟧)
    → Term ℓ A
  `case⊥ : ∀{ℓ A}
    → Term ℓ `⊥
    → Term ℓ A
  `caseBool : ∀{ℓ}
    (P : ⟦ ℓ ∣ `Bool ⟧ → Term (suc ℓ) `Type)
    (pt : Term ℓ (eval (P true)))
    (pf : Term ℓ (eval (P false)))
    (b : Term ℓ `Bool)
    → Term ℓ (eval (P (eval b)))
  `caseℕ : ∀{ℓ}
    (P : ⟦ ℓ ∣ `ℕ ⟧ → Term (suc ℓ) `Type)
    (pz : Term ℓ (eval (P zero)))
    (ps : (n : ⟦ ℓ ∣ `ℕ ⟧) → ⟦ ℓ ∣ eval (P n) ⟧ → Term ℓ (eval (P (suc n))))
    (n : Term ℓ `ℕ)
    → Term ℓ (eval (P (eval n)))
  `proj₁ : ∀{ℓ A B}
    (ab : Term ℓ (`Σ A B))
    → Term ℓ A
  `proj₂ : ∀{ℓ A B}
    (ab : Term ℓ (`Σ A B))
    → Term ℓ (B (proj₁ (eval ab)))
  _`$_ : ∀{ℓ A B}
    (f : Term ℓ (`Π A B)) (a : Term ℓ A)
    → Term ℓ (B (eval a))

----------------------------------------------------------------------

{- Type introduction -}
eval `⊥ = `⊥
eval `⊤ = `⊤
eval `Bool = `Bool
eval `ℕ = `ℕ
eval `Type = `Type
eval (`Π A B) = `Π (eval A) (λ a → eval (B a)) 
eval (`Σ A B) = `Σ (eval A) (λ a → eval (B a))
eval `⟦ A ⟧ = `⟦ eval A ⟧

{- Value introduction -}
eval `tt = tt
eval `true = true
eval `false = false
eval `zero = zero
eval (`suc n) = suc (eval n)
eval (`λ f) = λ a → eval (f a)
eval (a `, b) = eval a , eval b
eval (`lift a) = eval a

{- Value elimination -}
eval (`lower a) = eval a
eval (`case⊥ bot) = case⊥ (eval bot)
eval (`caseBool {ℓ = ℓ} P pt pf b) =
  caseBool (λ b → ⟦ ℓ ∣ eval (P b) ⟧)
    (eval pt) (eval pf) (eval b)
eval (`caseℕ {ℓ = ℓ} P pz ps n) =
  caseℕ (λ n → ⟦ ℓ ∣ eval (P n) ⟧)
    (eval pz) (λ n pn → eval (ps n pn)) (eval n)
eval (`proj₁ ab) = proj₁ (eval ab)
eval (`proj₂ ab) = proj₂ (eval ab)
eval (f `$ a) = (eval f) (eval a)

----------------------------------------------------------------------
