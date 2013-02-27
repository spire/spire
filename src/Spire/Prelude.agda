module Spire.Prelude where
{-# IMPORT Spire.Parser #-}

----------------------------------------------------------------------

data ⊥ : Set where
record ⊤ : Set where constructor tt

data Bool : Set where true false : Bool
{-# COMPILED_DATA Bool Bool True False #-}
{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

----------------------------------------------------------------------

data Maybe (A : Set) : Set where
  just : (x : A) → Maybe A
  nothing : Maybe A
{-# COMPILED_DATA Maybe Maybe Just Nothing #-}

----------------------------------------------------------------------

infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B
{-# COMPILED_DATA _⊎_ Either Left Right #-}

----------------------------------------------------------------------

infixr 2 _×_
data _×_ (A B : Set) : Set where
  _,_ : (a : A) (b : B) → A × B
{-# COMPILED_DATA _×_ (,) (,) #-}

----------------------------------------------------------------------

infixr 4 _,_
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁
open Σ public

----------------------------------------------------------------------

record Universe : Set₁ where
  field
    Codes : Set
    Meaning : Codes → Set
open Universe public

----------------------------------------------------------------------

infix 4 _≅_
data _≅_ {A : Set} (a : A) : {B : Set} → B → Set where
  refl : a ≅ a

cong : ∀ {A : Set} {B : A → Set} {x y}
       (f : (x : A) → B x) → x ≅ y → f x ≅ f y
cong f refl = refl

cong₂ : ∀ {A : Set} {B : A → Set} {C : ∀ x → B x → Set}
          {x y u v}
        (f : (x : A) (y : B x) → C x y) → x ≅ y → u ≅ v → f x u ≅ f y v
cong₂ f refl refl = refl

----------------------------------------------------------------------

data ℕ : Set where
  zero : ℕ
  suc : (n : ℕ) → ℕ

{-# COMPILED_DATA ℕ Spire.Parser.Nat
  Spire.Parser.Zero Spire.Parser.Succ
#-}
{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)
{-# BUILTIN NATPLUS _+_ #-}

infixl 6 _∸_
_∸_ : ℕ → ℕ → ℕ
m     ∸ zero  = m
zero  ∸ suc n = zero
suc m ∸ suc n = m ∸ n
{-# BUILTIN NATMINUS _∸_ #-}

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + m * n
{-# BUILTIN NATTIMES _*_ #-}

----------------------------------------------------------------------

data List (A : Set) : Set where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A
{-# COMPILED_DATA List [] [] (:) #-}
{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}

----------------------------------------------------------------------

postulate Int : Set
{-# BUILTIN INTEGER Int #-}
{-# COMPILED_TYPE Int Int #-}

private
  primitive primIntegerAbs : Int → ℕ

abs = primIntegerAbs

----------------------------------------------------------------------

postulate String : Set
{-# BUILTIN STRING String #-}
{-# COMPILED_TYPE String String #-}

private
 primitive
  primStringAppend   : String → String → String
  primStringEquality : String → String → Bool

infixr 5 _++_
_++_ = primStringAppend

infix 4 _==_
_==_ = primStringEquality

----------------------------------------------------------------------

data Unit : Set where unit : Unit
{-# COMPILED_DATA Unit () () #-}

postulate IO : Set → Set
{-# COMPILED_TYPE IO IO #-}
{-# BUILTIN IO IO #-}

----------------------------------------------------------------------

const : {A B : Set} → A → B → A
const x = λ _ → x

----------------------------------------------------------------------
