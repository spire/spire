{-
Demonstrating the technique of using type-changing functions
to pattern match against types with higher-order arguments
like Σ and Π.

The technique was originally explored to compare higher-order
small arguments that occur in Φ types in
TacticsMatchingFunctionCalls.agda

This file shows that the technique scales to large higher-order
functions , in a closed universe with a predicative hierarchy
of levels that supports elimType.

-}

open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Fin hiding ( _+_ )
open import Data.Fin.Props
open import Data.Product
open import Data.String
open import Function
open import Relation.Binary.PropositionalEquality hiding ( inspect )
open Deprecated-inspect
module HierMatchExt where

----------------------------------------------------------------------

plusrident : (n : ℕ) → n + 0 ≡ n
plusrident zero = refl
plusrident (suc n) = cong suc (plusrident n)

----------------------------------------------------------------------

record Universe : Set₁ where
  field
    Codes : Set
    Meaning : Codes → Set

----------------------------------------------------------------------

data Even : ℕ → Set where
  ezero : Even 0
  esuc : {n : ℕ} → Even n → Even (2 + n)

data Odd : ℕ → Set where
  ozero : Odd 1
  osuc : {n : ℕ} → Odd n → Odd (2 + n)

----------------------------------------------------------------------

data TypeForm (U : Universe) : Set
⟦_/_⟧ : (U : Universe) → TypeForm U → Set

data TypeForm U where
  `⊥ `⊤ `Bool `ℕ `Type : TypeForm U
  `Fin `Even `Odd : (n : ℕ) → TypeForm U
  `Π `Σ : (A : TypeForm U)
    (B : ⟦ U / A ⟧ → TypeForm U)
    → TypeForm U
  `Id : (A : TypeForm U) (x y : ⟦ U / A ⟧) → TypeForm U
  `⟦_⟧ : (A : Universe.Codes U) → TypeForm U

⟦ U / `⊥ ⟧ = ⊥
⟦ U / `⊤ ⟧ = ⊤
⟦ U / `Bool ⟧ = Bool
⟦ U / `ℕ ⟧ = ℕ
⟦ U / `Fin n ⟧ = Fin n
⟦ U / `Even n ⟧ = Even n
⟦ U / `Odd n ⟧ = Odd n
⟦ U / `Π A B ⟧ = (a : ⟦ U / A ⟧) → ⟦ U / B a ⟧
⟦ U / `Σ A B ⟧ = Σ ⟦ U / A ⟧ (λ a → ⟦ U / B a ⟧)
⟦ U / `Id A x y ⟧ = _≡_ {A = ⟦ U / A ⟧} x y
⟦ U / `Type ⟧ = Universe.Codes U
⟦ U / `⟦ A ⟧ ⟧ = Universe.Meaning U A

----------------------------------------------------------------------

_`→_ : ∀{U} (A B : TypeForm U) → TypeForm U
A `→ B = `Π A (λ _ → B)

_`×_ : ∀{U} (A B : TypeForm U) → TypeForm U
A `× B = `Σ A (λ _ → B)

Level : (ℓ : ℕ) → Universe
Level zero = record { Codes = ⊥ ; Meaning = λ() }
Level (suc ℓ) = record { Codes = TypeForm (Level ℓ)
                       ; Meaning = ⟦_/_⟧ (Level ℓ) }

Type : ℕ → Set
Type ℓ = TypeForm (Level ℓ)

⟦_∣_⟧ : (ℓ : ℕ) → Type ℓ → Set
⟦ ℓ ∣ A ⟧ = ⟦ Level ℓ / A ⟧

`Dynamic : (ℓ : ℕ) → Type (suc ℓ)
`Dynamic ℓ = `Σ `Type `⟦_⟧

`Tactic : (ℓ : ℕ) → Type (suc ℓ)
`Tactic ℓ = `Dynamic ℓ `→ `Dynamic ℓ

Tactic : (ℓ : ℕ) → Set
Tactic ℓ = ⟦ suc ℓ ∣ `Tactic ℓ ⟧

----------------------------------------------------------------------

rm-plus0-Fin : (ℓ : ℕ) → Tactic (suc ℓ)
rm-plus0-Fin ℓ (`⟦ `Σ `ℕ B ⟧ , (n , b))
  with inspect (B n)
... | `Fin m with-≡ p =
  `Π `ℕ (λ x → `Id `Type (B x) (`Fin (x + 0)))
  `→
  `Σ `ℕ `Fin
  ,
  λ f → n , subst Fin
    (plusrident n)
    (subst (λ A → ⟦ ℓ ∣ A ⟧) (f n) b)
... | Bn with-≡ p = (`⟦ `Σ `ℕ B ⟧ , (n , subst (λ x → ⟦ ℓ ∣ B x ⟧) refl b))
rm-plus0-Fin ℓ x = x

----------------------------------------------------------------------

-- eg-rm-plus0-Fin : (ℓ : ℕ) →
--   ⟦ suc ℓ ∣ `⟦ `Σ `ℕ (λ n → `Fin (n + zero)) ⟧
--         `→ `⟦ `Σ `ℕ (λ n → `Fin n) ⟧ ⟧
-- eg-rm-plus0-Fin ℓ (n , i) = proj₂
--   (rm-plus0-Fin ℓ (`⟦ `Σ `ℕ (λ n → `Fin (n + zero)) ⟧ , (n , i)))
--   (λ _ → refl)

----------------------------------------------------------------------
