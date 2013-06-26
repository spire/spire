{- 
This file demonstrates a technique that simulates the ability to
pattern match against function calls rather than just variables
or constructors.

This technique is necessary to write certain kinds of tactics
as generic functions.
-}

module TacticsMatchingFunctionCalls where
open import Data.Bool hiding ( _≟_ )
open import Data.Nat
open import Data.Fin hiding ( _+_ )
open import Data.Product hiding ( map )
open import Data.List
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Function

----------------------------------------------------------------------

{-
Zero is the right identity of addition on the natural numbers.
-}

plusrident : (n : ℕ) → n ≡ n + 0
plusrident zero = refl
plusrident (suc n) = cong suc (plusrident n)

----------------------------------------------------------------------

{-
Arith is a universe of codes representing the natural numbers
along with a limited set of functions over them. We would like to write
tactics that pattern match against types indexed by applications of
these functions.
-}

data Arith : Set where
  `zero : Arith
  `suc : (a : Arith) → Arith
  _`+_ _`*_ : (a₁ a₂ : Arith) → Arith

eval : Arith → ℕ
eval `zero = zero
eval (`suc a) = suc (eval a)
eval (a₁ `+ a₂) = eval a₁ + eval a₂
eval (a₁ `* a₂) = eval a₁ * eval a₂

----------------------------------------------------------------------

{-
Φ (standing for *function*-indexed types)
represents an indexed type, but we *can* pattern
match on function calls in its index position.

A - The type of codes, including constructors and functions.
  i.e. Arith
A′ - The model underlying the codes.
  i.e. ℕ
el - The evaluation function from code values to model values.
  i.e. eval
B - The genuine indexed datatype that Φ represents.
  i.e. Fin
a - The index value as a code, which may be a function call and hence supports
    pattern matching.
  i.e. (a `+ `zero)
-}

data Φ (A A′ : Set) (el : A → A′) (B : A′ → Set) (a : A) : Set where
  φ : (b : B (el a)) → Φ A A′ el B a

----------------------------------------------------------------------

{-
Alternatively, we can specialize Φ to our Arith universe. This may be
a good use of our ability to cheaply define new datatypes via Desc.
-}

data ΦArith (B : ℕ → Set) (a : Arith) : Set where
  φ : (b : B (eval a)) → ΦArith B a

----------------------------------------------------------------------

{-
Going further, we could even specialize B in ΦArith to Fin.
-}

data Fin₂ (a : Arith) : Set where
  fin : (i : Fin (eval a)) → Fin₂ a

----------------------------------------------------------------------

{-
A small universe of dependent types that is sufficient for the
examples given below.
-}

data Type : Set
⟦_⟧ : Type → Set

data Type where
  `Bool `ℕ `Arith : Type
  `Fin : (n : ℕ) → Type
  `Φ : (A A′ : Type)
    (el : ⟦ A ⟧ → ⟦ A′ ⟧)
    (B : ⟦ A′ ⟧ → Type)
    (a : ⟦ A ⟧)
    → Type
  `ΦArith : (B : ℕ → Type) (a : Arith) → Type
  `Fin₂ : (a : Arith) → Type
  `Π `Σ : (A : Type) (B : ⟦ A ⟧ → Type) → Type
  `Id : (A : Type) (x y : ⟦ A ⟧) → Type

⟦ `Bool ⟧ = Bool
⟦ `ℕ ⟧ = ℕ
⟦ `Arith ⟧ = Arith
⟦ `Fin n ⟧ = Fin n
⟦ `Φ A A′ el B a ⟧ = Φ ⟦ A ⟧ ⟦ A′ ⟧ el (λ a → ⟦ B a ⟧) a
⟦ `ΦArith B a ⟧ = ΦArith (λ x → ⟦ B x ⟧) a
⟦ `Fin₂ a ⟧ = Fin₂ a
⟦ `Π A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
⟦ `Σ A B ⟧ = Σ ⟦ A ⟧ (λ a → ⟦ B a ⟧)
⟦ `Id A x y ⟧ = x ≡ y

_`→_ : (A B : Type) → Type
A `→ B = `Π A (const B)

_`×_ : (A B : Type) → Type
A `× B = `Σ A (const B)

----------------------------------------------------------------------

{-
Tactics are represented as generic functions taking a Dynamic value (of
any type), and returning a Dynamic value (at a possibly different type).
The convention is to behave like the identity function if the tactic
doesn't match the current value or fails.

In practice, the context will be a List of Dynamic values, and a tactic
will map a Context to a Context. For simplicity, the tactics I give below
only map a Dynamic to a Dynamic.
-}

Dynamic : Set
Dynamic = Σ Type ⟦_⟧

Tactic : Set
Tactic = Dynamic → Dynamic

----------------------------------------------------------------------

{-
Here is an example of a tactic that only needs to pattern match on a
variable or constructor, but not a function. We don't encounter
any problems when writing this kind of a tactic.

The tactic below changes a `Fin n` value into a `Fin (n + 0)` value.
-}

add-plus0-Fin : Tactic
add-plus0-Fin (`Fin n , i) = `Fin (n + 0) , subst Fin (plusrident n) i
add-plus0-Fin x = x

----------------------------------------------------------------------

{-
In contrast, it is not straightforward to write tactics that need
to pattern match on function calls.
For example, below is ideally what we want to write to change
a value of `Fin (n + 0)` to a value of `Fin n`.
-}

-- rm-plus0-Fin : Tactic
-- rm-plus0-Fin (`Fin (n + 0) , i) = `Fin n , subst Fin (sym (plusrident n)) i
-- rm-plus0-Fin x = x

----------------------------------------------------------------------

{-
Instead of matching directly on `Fin, we can match on a `Φ that
represents `Fin. This allows us to match on the the `+ function call
in the index position.

Because we cannot match against the function `el` (we would like to match
it against `eval`), we add to our return type that proves the
extentional equality between `el` and `eval`.

Also note that the tactic below can be used for any type indexed by
ℕ, not just Fin.
-}

rm-plus0 : Tactic
rm-plus0 (`Φ `Arith `ℕ el B (a `+ `zero) , φ b) =
  `Π `Arith (λ x → `Id `ℕ (el x) (eval x))
  `→
  `Φ `Arith `ℕ el B a
  ,
  λ f → φ
  (subst (λ x → ⟦ B x ⟧)
         (sym (f a))
         (subst (λ x → ⟦ B x ⟧)
                (sym (plusrident (eval a)))
                (subst (λ x → ⟦ B x ⟧)
                       (f (a `+ `zero))
                       b)))
rm-plus0 x = x

----------------------------------------------------------------------

{-
Now it is possible to apply the generic tactic to a specific
value and have the desired behavior occur. Notice that the generated
extentional equality premise is trivially provable because
eval is always equal to eval.
-}

eg-rm-plus0 : (a : Arith)
  → ⟦ `Φ `Arith `ℕ eval `Fin (a `+ `zero) ⟧
  → ⟦ `Φ `Arith `ℕ eval `Fin a ⟧
eg-rm-plus0 a (φ i) = proj₂
  (rm-plus0 (`Φ `Arith `ℕ eval `Fin (a `+ `zero) , φ i))
  (λ _ → refl)

----------------------------------------------------------------------

{-
Here is the same tactic but using the specialized ΦArith type.
-}

rm-plus0-Arith : Tactic
rm-plus0-Arith (`ΦArith B (a `+ `zero) , φ i) =
  `ΦArith B a
  ,
  φ (subst (λ x → ⟦ B x ⟧) (sym (plusrident (eval a))) i)
rm-plus0-Arith x = x

----------------------------------------------------------------------

{-
And the same example usage, this time without needing to prove a premise.
-}

eg-rm-plus0-Arith : (a : Arith)
  → ⟦ `ΦArith `Fin (a `+ `zero) ⟧
  → ⟦ `ΦArith `Fin a ⟧
eg-rm-plus0-Arith a (φ i) = proj₂
  (rm-plus0-Arith (`ΦArith `Fin (a `+ `zero) , φ i))

----------------------------------------------------------------------

{-
Finally, here is the same tactic but using the even more 
specialized Fin₂ type.
-}

rm-plus0-Fin : Tactic
rm-plus0-Fin (`Fin₂ (a `+ `zero) , fin i) =
  `Fin₂ a
  ,
  fin (subst (λ x → ⟦ `Fin x ⟧) (sym (plusrident (eval a))) i)
rm-plus0-Fin x = x

----------------------------------------------------------------------

eg-rm-plus0-Fin : (a : Arith)
  → ⟦ `Fin₂ (a `+ `zero) ⟧
  → ⟦ `Fin₂ a ⟧
eg-rm-plus0-Fin a (fin i) = proj₂
  (rm-plus0-Fin (`Fin₂ (a `+ `zero) , fin i))

----------------------------------------------------------------------
