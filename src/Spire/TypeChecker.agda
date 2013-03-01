open import Spire.Prelude
open import Spire.Evaluator
module Spire.TypeChecker where
{-# IMPORT Spire.Parser #-}

----------------------------------------------------------------------

data Equal {A : Set} : A → A → Set where
  yes : {a : A} → Equal a a
  no : {a b : A} → Equal a b

compareT : ∀{Γ} → (A B : Type Γ) → Equal A B
compareV : ∀{Γ} {A : Type Γ} (a b : Val Γ A) → Equal a b
compareNV : ∀{Γ} {A : Type Γ} (a b : NVal Γ A) → Equal a b
compareR : ∀{Γ} {A : Type Γ} (i j : Var Γ A) → Equal i j

compareT (`wkn A) (`wkn A′) with compareT A A′
compareT (`wkn A) (`wkn ._) | yes = yes
compareT (`wkn A) (`wkn A′) | no = no
compareT `⊤ `⊤ = yes
compareT `Bool `Bool = yes
compareT (A `→ B) (A′ `→ B′) with compareT A A′
compareT (A `→ B) (.A `→ B′) | yes with compareT B B′
compareT (A `→ B) (.A `→ .B) | yes | yes = yes
compareT (A `→ B) (.A `→ B′) | yes | no = no
compareT (A `→ B) (A′ `→ B′) | no = no
compareT (`neutral (`if b then A else B)) (`neutral (`if b′ then A′ else B′))
  with compareNV b b′
compareT (`neutral (`if b then A else B)) (`neutral (`if ._ then A′ else B′)) | yes
  with compareT A A′
compareT (`neutral (`if b then A else B)) (`neutral (`if .b then ._ else B′)) | yes | yes
  with compareT B B′
compareT (`neutral (`if b then A else B)) (`neutral (`if .b then ._ else ._)) | yes | yes | yes = yes
compareT (`neutral (`if b then A else B)) (`neutral (`if .b then ._ else B′)) | yes | yes | no = no
compareT (`neutral (`if b then A else B)) (`neutral (`if .b then A′ else B′)) | yes | no = no
compareT (`neutral (`if b then A else B)) (`neutral (`if b′ then A′ else B′)) | no = no
compareT _ _ = no

compareV (`wkn a) (`wkn a′) with compareV a a′
compareV (`wkn a) (`wkn .a) | yes = yes
compareV (`wkn a) (`wkn a′) | no = no
compareV `tt `tt = yes
compareV `true `true = yes
compareV `false `false = yes
compareV (`λ f) (`λ f′) with compareV f f′
compareV (`λ .f′) (`λ f′) | yes = yes
compareV (`λ f) (`λ f′) | no = no
compareV (`neutral a) (`neutral a′) with compareNV a a′
compareV (`neutral .a′) (`neutral a′) | yes = yes
compareV (`neutral a) (`neutral a′) | no = no
compareV _ _ = no

compareNV (`var i) (`var i′) with compareR i i′
compareNV (`var i) (`var ._) | yes = yes
compareNV (`var i) (`var i′) | no = no
compareNV (`not a) (`not a′) with compareNV a a′
compareNV (`not a) (`not ._) | yes = yes
compareNV (`not a) (`not a′) | no = no
compareNV (_`$_ {A = A} f a) (_`$_ {A = A′} f′ a′) with compareT A A′
compareNV (f `$ a) (f′ `$ a′) | yes with compareNV f f′
compareNV (.f′ `$ a) (f′ `$ a′) | yes | yes with compareV a a′
compareNV (.f′ `$ .a′) (f′ `$ a′) | yes | yes | yes = yes
compareNV (.f′ `$ a) (f′ `$ a′) | yes | yes | no = no
compareNV (f `$ a) (f′ `$ a′) | yes | no = no
compareNV (f `$ a) (f′ `$ a′) | no = no
compareNV _ _ = no

compareR here here = yes
compareR here (there j) = no
compareR (there i) here = no
compareR (there i) (there j) with compareR i j
compareR (there i) (there ._) | yes = yes
compareR (there i) (there j) | no = no

----------------------------------------------------------------------

index : ∀{Γ A} → Var Γ A → ℕ
index here = zero
index (there i) = suc (index i)

length : Con → ℕ
length ∅ = zero
length (Γ , A) = suc (length Γ)

data Lookup (Γ : Con) : ℕ → Set where
  inside : (A : Type Γ) (i : Var Γ A) → Lookup Γ (index i)
  outside : (n : ℕ) → Lookup Γ (length Γ + n)

lookup : (Γ : Con) (n : ℕ) → Lookup Γ n
lookup ∅ n = outside n
lookup (Γ , A) zero = inside (`wkn A) here
lookup (Γ , A) (suc n) with lookup Γ n
lookup (Γ , B) (suc .(index i)) | inside A i = inside (`wkn A) (there i)
lookup (Γ , B) (suc .(length Γ + n)) | outside n = outside n

----------------------------------------------------------------------

data PreTerm : Set where
  `wkn : (a : PreTerm) → PreTerm
  `var : ℕ → PreTerm
  `tt `true `false : PreTerm
  `λ : PreTerm → PreTerm
  `not : (b : PreTerm) → PreTerm

{-# COMPILED_DATA PreTerm Spire.Parser.Term
  Spire.Parser.WknV
  Spire.Parser.Var Spire.Parser.TT
  Spire.Parser.True Spire.Parser.False
  Spire.Parser.Lam
  Spire.Parser.Not
#-}

data PreType : Set where
  `wkn : (A : PreType) → PreType
  `⊤ `Bool : PreType
  _`→_ : (A B : PreType) → PreType
  `if_then_else_ : (b : PreTerm)
    (A B : PreType)
    → PreType

{-# COMPILED_DATA PreType Spire.Parser.Type
  Spire.Parser.Wkn
  Spire.Parser.Unit Spire.Parser.Bool
  Spire.Parser.Arr
  Spire.Parser.If
#-}

eraseType : ∀{Γ} → TermType Γ → PreType
erase : ∀{Γ A} → Term Γ A → PreTerm

eraseType (`wkn A) = `wkn (eraseType A)
eraseType `⊤ = `⊤
eraseType `Bool = `Bool
eraseType (`if b then A else B) = `if erase b then eraseType A else eraseType B
eraseType (A `→ B) = eraseType A `→ eraseType B

erase (`wkn a) = `wkn (erase a)
erase (`var i) = `var (index i)
erase `tt = `tt
erase `true = `true
erase `false = `false
erase (`λ f) = `λ (erase f)
erase (`not b) = `not (erase b)
erase (f `$ a) = `tt -- TODO implement application

----------------------------------------------------------------------

data CheckType (Γ : Con) : PreType → Set where
  well :  (A : TermType Γ) → CheckType Γ (eraseType A)
  ill : ∀{A} (x : PreType) (msg : String) → CheckType Γ A

data Check (Γ : Con) (A : Type Γ) : PreTerm → Set where
  well :  (a : Term Γ A) → Check Γ A (erase a)
  ill : ∀{a} (x : PreTerm) (msg : String) → Check Γ A a

checkT : (Γ : Con) (A : PreType) → CheckType Γ A
check : (Γ : Con) (A : Type Γ) (a : PreTerm) → Check Γ A a

checkT ∅ (`wkn A) = ill (`wkn A) "type is not weakened in empty context."
checkT (Γ , B) (`wkn A) with checkT Γ A
checkT (Γ , B) (`wkn ._) | well A = well (`wkn A)
checkT (Γ , B) (`wkn A) | ill x msg = ill x msg
checkT Γ `⊤ = well `⊤
checkT Γ `Bool = well `Bool
checkT Γ (A `→ B) with checkT Γ A
checkT Γ (._ `→ B) | well A with checkT Γ B
checkT Γ (._ `→ ._) | well A | well B = well (A `→ B)
checkT Γ (._ `→ B) | well A | ill x msg = ill x msg
checkT Γ (A `→ B) | ill x msg = ill x msg
checkT Γ (`if b then A else B) with check Γ `Bool b
checkT Γ (`if ._ then A else B) | well b with checkT Γ A
checkT Γ (`if ._ then ._ else B) | well b | well A with checkT Γ B
checkT Γ (`if ._ then ._ else ._) | well b | well A | well B = well (`if b then A else B)
checkT Γ (`if ._ then ._ else B) | well b | well A | ill x msg = ill x msg
checkT Γ (`if ._ then A else B) | well b | ill x msg = ill x msg  
checkT Γ (`if b then A else B) | ill x msg = ill (`if b then A else B) msg

check Γ A (`var i) with lookup Γ i
check Γ A (`var ._) | inside B i with compareT A B
check Γ .B (`var ._) | inside B i | yes = well (`var i)
check Γ A (`var ._) | inside B i | no = ill (`var (index i)) "type in context does not match checked type." 
check Γ A (`var ._) | outside n = ill (`var (length Γ + n)) "is not in the context."
check ._ (`wkn {Γ} A) (`wkn a) with check Γ A a
check ._ (`wkn {Γ} A) (`wkn ._) | well a = well (`wkn a)
check ._ (`wkn {Γ} A) (`wkn a) | ill x msg = ill x msg
check ._ (`wkn A) a = ill a "is not a weakened type."
check Γ (`neutral A) a = ill a "is not a neutral type."
check Γ `Bool (`not b) with check Γ `Bool b
check Γ `Bool (`not ._) | well b = well (`not b)
check Γ `Bool (`not b) | ill x msg = ill x msg
check Γ `⊤ `tt = well `tt
check Γ `⊤ x = ill x "is not a unit."
check Γ `Bool `true = well `true
check Γ `Bool `false = well `false
check Γ `Bool x = ill x "is not a bool."
check Γ (A `→ B) (`λ f) with check (Γ , A) (`wkn B) f
check Γ (A `→ B) (`λ ._) | well f = well (`λ f)
check Γ (A `→ B) (`λ f) | ill x msg = ill x msg
check Γ (A `→ B) x = ill x "is not a function."

----------------------------------------------------------------------

TypeChecker = (A : PreType) (a : PreTerm) → PreType × PreTerm ⊎ PreType × String ⊎ PreTerm × String
checkType : TypeChecker
checkType A a with checkT ∅ A
checkType ._ a | well A with check ∅ (evalType A) a
checkType ._ .(erase a) | well A | well a = inj₁ (eraseType (embT (evalType A)) , erase (embV (eval a)))
checkType ._ a | well A | ill x msg = inj₂ (inj₂ (x , msg))
checkType A a | ill x msg = inj₂ (inj₁ (x , msg))

----------------------------------------------------------------------
