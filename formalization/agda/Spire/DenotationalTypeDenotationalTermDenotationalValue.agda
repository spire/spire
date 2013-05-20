open import Spire.DenotationalType
module Spire.DenotationalTypeDenotationalTermDenotationalValue where

----------------------------------------------------------------------

data Term : Set → Set₁
eval : {A : Set} → Term A → A

----------------------------------------------------------------------

data Term where
  {- Type introduction -}
  `⊥ `⊤ `Bool `ℕ `Type : ∀{ℓ} → Term (Type (suc ℓ))
  `Π `Σ : ∀{ℓ}
    (A : Term (Type (suc ℓ)))
    (B : ⟦ suc ℓ ∣ eval A ⟧ → Term (Type (suc ℓ)))
    → Term (Type (suc ℓ))
  `⟦_⟧ : ∀{ℓ}
    (A : Term (Type ℓ))
    → Term (Type (suc ℓ))

  {- Value introduction -}
  `tt : Term ⊤
  `true `false : Term Bool
  `zero : Term ℕ
  `suc : Term ℕ → Term ℕ
  `λ : ∀{A} {B : A → Set}
    (f : (a : A) → Term (B a))
    → Term ((a : A) → B a)
  _`,_ : ∀{A B}
    (a : Term A)
    (b : Term (B (eval a)))
    → Term (Σ A B)

  {- Value elimination -}
  `elim⊥ : ∀{A}
    → Term ⊥
    → Term A
  `elimBool : ∀{ℓ}
    (P : Bool → Term (Type (suc ℓ)))
    (pt : Term ⟦ suc ℓ ∣ eval (P true) ⟧)
    (pf : Term ⟦ suc ℓ ∣ eval (P false) ⟧)
    (b : Term Bool)
    → Term ⟦ suc ℓ ∣ eval (P (eval b)) ⟧
  `elimℕ : ∀{ℓ}
    (P : ℕ → Term (Type (suc ℓ)))
    (pz : Term ⟦ suc ℓ ∣ eval (P zero) ⟧)
    (ps : (n : ℕ) → ⟦ suc ℓ ∣ eval (P n) ⟧ → Term ⟦ suc ℓ ∣ eval (P (suc n)) ⟧)
    (n : Term ℕ)
    → Term ⟦ suc ℓ ∣ eval (P (eval n)) ⟧
  `proj₁ : ∀{A B}
    (ab : Term (Σ A B))
    → Term A
  `proj₂ : ∀{A B}
    (ab : Term (Σ A B))
    → Term (B (proj₁ (eval ab)))
  _`$_ : ∀{A} {B : A → Set}
    (f : Term ((a : A) → B a))
    (a : Term A)
    → Term (B (eval a))

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

{- Value elimination -}
eval (`elim⊥ bot) = elim⊥ (eval bot)
eval (`elimBool {ℓ = ℓ} P pt pf b) =
  elimBool (λ b → ⟦ suc ℓ ∣ eval (P b) ⟧)
    (eval pt) (eval pf) (eval b)
eval (`elimℕ {ℓ = ℓ} P pz ps n) =
  elimℕ (λ n → ⟦ suc ℓ ∣ eval (P n) ⟧)
    (eval pz) (λ n pn → eval (ps n pn)) (eval n)
eval (`proj₁ ab) = proj₁ (eval ab)
eval (`proj₂ ab) = proj₂ (eval ab)
eval (f `$ a) = (eval f) (eval a)

----------------------------------------------------------------------
