module Spire.DenotationalType where

----------------------------------------------------------------------

data ⊥ : Set where
record ⊤ : Set where constructor tt
data Bool : Set where true false : Bool

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁
open Σ public

----------------------------------------------------------------------

const : {A : Set₁} {B : Set} → A → B → A
const a _ = a

uncurry : {A : Set} {B : A → Set} {C : Σ A B → Set} →
  ((a : A) → (b : B a) → C (a , b)) →
  ((p : Σ A B) → C p)
uncurry f (a , b) = f a b

----------------------------------------------------------------------

record Universe : Set₁ where
  field
    Codes : Set
    Meaning : Codes → Set

----------------------------------------------------------------------

data TypeForm (U : Universe) : Set
⟦_/_⟧ : (U : Universe) → TypeForm U → Set

data TypeForm U where
  `⊥ `⊤ `Bool `ℕ : TypeForm U
  `Π `Σ : (A : TypeForm U)
    (B : ⟦ U / A ⟧ → TypeForm U)
    → TypeForm U
  `Type : TypeForm U
  `⟦_⟧ : Universe.Codes U → TypeForm U

⟦ U / `⊥ ⟧ = ⊥
⟦ U / `⊤ ⟧ = ⊤
⟦ U / `Bool ⟧ = Bool
⟦ U / `ℕ ⟧ = ℕ
⟦ U / `Π A B ⟧ = (a : ⟦ U / A ⟧) → ⟦ U / B a ⟧
⟦ U / `Σ A B ⟧ = Σ ⟦ U / A ⟧ (λ a → ⟦ U / B a ⟧)
⟦ U / `Type ⟧ = Universe.Codes U
⟦ U / `⟦ A ⟧ ⟧ = Universe.Meaning U A

----------------------------------------------------------------------

_`→_ : ∀{U} (A B : TypeForm U) → TypeForm U
A `→ B = `Π A (λ _ → B)

Level : (ℓ : ℕ) → Universe
Level zero = record { Codes = ⊥ ; Meaning = λ() }
Level (suc ℓ) = record { Codes = TypeForm (Level ℓ)
                       ; Meaning = ⟦_/_⟧ (Level ℓ) }

Type : ℕ → Set
Type ℓ = TypeForm (Level ℓ)

infix 0 ⟦_∣_⟧
⟦_∣_⟧ : (ℓ : ℕ) → Type ℓ → Set
⟦ ℓ ∣ A ⟧ = ⟦ Level ℓ / A ⟧

----------------------------------------------------------------------

elim⊥ : {A : Set} → ⊥ → A
elim⊥ ()

elimBool : (P : Bool → Set)
  (pt : P true)
  (pf : P false)
  (b : Bool) → P b
elimBool P pt pf true = pt
elimBool P pt pf false = pf

elimℕ : (P : ℕ → Set)
  (pz : P zero)
  (ps : (n : ℕ) → P n → P (suc n))
  (n : ℕ) → P n
elimℕ P pz ps zero = pz
elimℕ P pz ps (suc n) = ps n (elimℕ P pz ps n)

lift : ∀{ℓ} {A : Type ℓ} → ⟦ ℓ ∣ A ⟧ → ⟦ suc ℓ ∣ `⟦ A ⟧ ⟧
lift x = x

lower : ∀{ℓ} {A : Type ℓ} → ⟦ suc ℓ ∣ `⟦ A ⟧ ⟧ → ⟦ ℓ ∣ A ⟧
lower x = x

elimType : (P : (ℓ : ℕ) → Type ℓ → Set)
  → ((ℓ : ℕ) → P ℓ `⊥)
  → ((ℓ : ℕ) → P ℓ `⊤)
  → ((ℓ : ℕ) → P ℓ `Bool)
  → ((ℓ : ℕ) → P ℓ `ℕ)
  → ((ℓ : ℕ) (A : Type ℓ) (B : ⟦ ℓ ∣ A ⟧ → Type ℓ)
    (rec₁ : P ℓ A)
    (rec₂ : (a : ⟦ ℓ ∣ A ⟧) → P ℓ (B a))
    → P ℓ (`Π A B))
  → ((ℓ : ℕ) (A : Type ℓ) (B : ⟦ ℓ ∣ A ⟧ → Type ℓ)
    (rec₁ : P ℓ A)
    (rec₂ : (a : ⟦ ℓ ∣ A ⟧) → P ℓ (B a))
    → P ℓ (`Σ A B))
  → ((ℓ : ℕ) → P ℓ `Type)
  → ((ℓ : ℕ) (A : Type ℓ) (rec : P ℓ A) → P (suc ℓ) `⟦ A ⟧)
  → (ℓ : ℕ) (A : Type ℓ) → P ℓ A

elimType P p⊥ p⊤ pBool pℕ pΠ pΣ pType p⟦A⟧
  ℓ `⊥ = p⊥ ℓ
elimType P p⊥ p⊤ pBool pℕ pΠ pΣ pType p⟦A⟧
  ℓ `⊤ = p⊤ ℓ
elimType P p⊥ p⊤ pBool pℕ pΠ pΣ pType p⟦A⟧
  ℓ `Bool = pBool ℓ
elimType P p⊥ p⊤ pBool pℕ pΠ pΣ pType p⟦A⟧
  ℓ `ℕ = pℕ ℓ
elimType P p⊥ p⊤ pBool pℕ pΠ pΣ pType p⟦A⟧
  ℓ (`Π A B) =
  let f = elimType P p⊥ p⊤ pBool pℕ pΠ pΣ pType p⟦A⟧ ℓ
  in pΠ ℓ A B (f A) (λ a → f (B a))
elimType P p⊥ p⊤ pBool pℕ pΠ pΣ pType p⟦A⟧
  ℓ (`Σ A B) =
  let f = elimType P p⊥ p⊤ pBool pℕ pΠ pΣ pType p⟦A⟧ ℓ
  in pΣ ℓ A B (f A) (λ a → f (B a))
elimType P p⊥ p⊤ pBool pℕ pΠ pΣ pType p⟦A⟧
  ℓ `Type = pType ℓ
elimType P p⊥ p⊤ pBool pℕ pΠ pΣ pType p⟦A⟧
  zero `⟦ () ⟧
elimType P p⊥ p⊤ pBool pℕ pΠ pΣ pType p⟦A⟧
  (suc ℓ) `⟦ A ⟧ =
  let f = elimType P p⊥ p⊤ pBool pℕ pΠ pΣ pType p⟦A⟧ ℓ
  in p⟦A⟧ ℓ A (f A)

----------------------------------------------------------------------
