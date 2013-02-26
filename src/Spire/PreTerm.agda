open import Spire.Prelude
open import Spire.Term
module Spire.PreTerm where
{-# IMPORT Spire.SurfaceTerm #-}

----------------------------------------------------------------------

data Equal {A : Set} : A → A → Set where
  yes : {a : A} → Equal a a
  no : {a b : A} → Equal a b

----------------------------------------------------------------------

index : ∀{Γ A} → Var Γ A → ℕ
index here = zero
index (there i) = suc (index i)

length : Con → ℕ
length ∅ = zero
length (Γ , A) = suc (length Γ)

data Lookup (Γ : Con) : ℕ → Set where
  inside : (A : Type) (i : Var Γ A) → Lookup Γ (index i)
  outside : (n : ℕ) → Lookup Γ (length Γ + n)

lookup : (Γ : Con) (n : ℕ) → Lookup Γ n
lookup ∅ n = outside n
lookup (Γ , A) zero = inside A here
lookup (Γ , A) (suc n) with lookup Γ n
lookup (Γ , B) (suc .(index i)) | inside A i = inside A (there i)
lookup (Γ , B) (suc .(length Γ + n)) | outside n = outside n

----------------------------------------------------------------------

data PreTerm : Set where
  `var : ℕ → PreTerm
  `tt `true `false : PreTerm
  `if_then_else_ : (b c₁ c₂ : PreTerm) → PreTerm

{-# COMPILED_DATA PreTerm Spire.SurfaceTerm.Term
  Spire.SurfaceTerm.Var Spire.SurfaceTerm.TT
  Spire.SurfaceTerm.True Spire.SurfaceTerm.False
  Spire.SurfaceTerm.If
#-}

erase : ∀{Γ A} → Term Γ A → PreTerm
erase (`var i) = `var (index i)
erase `tt = `tt
erase `true = `true
erase `false = `false
erase (`if b then c₁ else c₂) = `if erase b then erase c₁ else erase c₂

----------------------------------------------------------------------

data Check (Γ : Con) (A : Type) : PreTerm → Set where
  well :  (a : Term Γ A) → Check Γ A (erase a)
  ill : ∀{a} (x : PreTerm) (msg : String) → Check Γ A a

check : (Γ : Con) (A : Type) (a : PreTerm) → Check Γ A a
check Γ `⊤ (`var i) with lookup Γ i
check Γ `⊤ (`var .(index i)) | inside `⊤ i = well (`var i)
check Γ `⊤ (`var .(index i)) | inside A i = ill (`var (index i)) "does not have type ⊤." 
check Γ `⊤ (`var .(length Γ + n)) | outside n = ill (`var (length Γ + n)) "is not in the context."
check Γ `⊤ `tt = well `tt
check Γ `⊤ (`if b then c₁ else c₂) with check Γ `Bool b
check Γ `⊤ (`if ._ then c₁ else c₂) | well b with check Γ `⊤ c₁
check Γ `⊤ (`if ._ then ._ else c₂) | well b | well c₁ with check Γ `⊤ c₂
check Γ `⊤ (`if ._ then ._ else ._) | well b | well c₁ | well c₂ = well (`if b then c₁ else c₂)
check Γ `⊤ (`if ._ then ._ else c₂) | well b | well c₁ | ill x msg = ill x msg
check Γ `⊤ (`if ._ then c₁ else c₂) | well b | ill x msg = ill x msg
check Γ `⊤ (`if b then c₁ else c₂) | ill x msg = ill x msg
check Γ `⊤ x = ill x "does not have type ⊤."
check Γ `Bool (`var i) with lookup Γ i
check Γ `Bool (`var .(index i)) | inside `Bool i = well (`var i)
check Γ `Bool (`var .(index i)) | inside A i = ill (`var (index i)) "does not have type Bool." 
check Γ `Bool (`var .(length Γ + n)) | outside n = ill (`var (length Γ + n)) "is not in the context."
check Γ `Bool `true = well `true
check Γ `Bool `false = well `false
check Γ `Bool (`if b then c₁ else c₂) with check Γ `Bool b
check Γ `Bool (`if ._ then c₁ else c₂) | well b with check Γ `Bool c₁
check Γ `Bool (`if ._ then ._ else c₂) | well b | well c₁ with check Γ `Bool c₂
check Γ `Bool (`if ._ then ._ else ._) | well b | well c₁ | well c₂ = well (`if b then c₁ else c₂)
check Γ `Bool (`if ._ then ._ else c₂) | well b | well c₁ | ill x msg = ill x msg
check Γ `Bool (`if ._ then c₁ else c₂) | well b | ill x msg = ill x msg
check Γ `Bool (`if b then c₁ else c₂) | ill x msg = ill x msg
check Γ `Bool x = ill x "does not have type Bool."

----------------------------------------------------------------------

checkClosed = check ∅

TypeChecker = (A : Type) (a : PreTerm) → PreTerm ⊎ (PreTerm × String)
checkType : TypeChecker
checkType A a with checkClosed A a
checkType A .(erase a) | well a = inj₁ (erase (embV (eval a)))
checkType A a | ill x msg = inj₂ (x , msg)


