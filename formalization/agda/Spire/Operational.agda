module Spire.Operational where

----------------------------------------------------------------------

data Level : Set where
  zero : Level
  suc : Level → Level

----------------------------------------------------------------------

data Context : Set
data Type (Γ : Context) : Set
data Value (Γ : Context) : Type Γ → Set
data Neutral (Γ : Context) : Type Γ → Set

----------------------------------------------------------------------

data Context where
  ∅ : Context
  _,_ : (Γ : Context) → Type Γ → Context

data Type Γ where
  `⊥ `⊤ `Bool : Type Γ
  `Desc `Type : (ℓ : Level) → Type Γ
  `Π `Σ : (A : Type Γ) (B : Type (Γ , A)) → Type Γ
  `μ : ∀{ℓ} → Value Γ (`Desc ℓ) → Type Γ
  `⟦_⟧ : ∀{ℓ} → Neutral Γ (`Type ℓ) → Type Γ
  `⟦_⟧ᵈ : ∀{ℓ} → Neutral Γ (`Desc ℓ) → Type Γ → Type Γ

----------------------------------------------------------------------

⟦_⟧ : ∀{Γ ℓ} → Value Γ (`Type ℓ) →  Type Γ
⟦_⟧ᵈ : ∀{Γ ℓ} → Value Γ (`Desc ℓ) → Type Γ →  Type Γ

postulate
  wknT : ∀{Γ A} → Type Γ → Type (Γ , A)
  subT : ∀{Γ A} → Type (Γ , A) → Value Γ A → Type Γ
  subV : ∀{Γ A B} → Value (Γ , A) B → (x : Value Γ A) → Value Γ (subT B x)

data Var : (Γ : Context) (A : Type Γ) → Set where
  here : ∀{Γ A} → Var (Γ , A) (wknT A)
  there : ∀{Γ A B} → Var Γ A → Var (Γ , B) (wknT A)

----------------------------------------------------------------------

data Value Γ where
  {- Type introduction -}
  `⊥ `⊤ `Bool `Desc `Type : ∀{ℓ} → Value Γ (`Type ℓ)
  `Π `Σ : ∀{ℓ} (A : Value Γ (`Type ℓ)) (B : Value (Γ , ⟦ A ⟧) (`Type ℓ)) → Value Γ (`Type ℓ)
  `μ : ∀{ℓ} → Value Γ (`Desc ℓ) → Value Γ (`Type ℓ)
  `⟦_⟧ : ∀{ℓ} → Value Γ (`Type ℓ) → Value Γ (`Type (suc ℓ))
  `⟦_⟧ᵈ : ∀{ℓ} → Value Γ (`Desc ℓ) → Value Γ (`Type ℓ) → Value Γ (`Type ℓ)

  {- Desc introduction -}
  `⊤ᵈ `Xᵈ : ∀{ℓ} → Value Γ (`Desc ℓ)
  `Πᵈ `Σᵈ : ∀{ℓ}
    (A : Value Γ (`Type ℓ))
    (B : Value (Γ , ⟦ A ⟧) (`Desc (suc ℓ)))
    → Value Γ (`Desc (suc ℓ))

  {- Value introduction -}
  `tt : Value Γ `⊤
  `true `false : Value Γ `Bool
  _`,_ : ∀{A B} (a : Value Γ A) (b : Value Γ (subT B a)) → Value Γ (`Σ A B)
  `λ : ∀{A B} → Value (Γ , A) B → Value Γ (`Π A B)
  `con : ∀{ℓ} {D : Value Γ (`Desc ℓ)} → Value Γ (⟦ D ⟧ᵈ (`μ D)) → Value Γ (`μ D)
  `neut : ∀{A} → Neutral Γ A → Value Γ A

----------------------------------------------------------------------

data Neutral Γ where
  {- Value elimination -}
  `var : ∀{A} → Var Γ A → Neutral Γ A
  `if_`then_`else_ : ∀{C} (b : Neutral Γ `Bool) (c₁ c₂ : Value Γ C) → Neutral Γ C
  `elim⊥ : ∀{A} → Neutral Γ `⊥ → Neutral Γ A
  `elimBool : ∀{ℓ} (P : Value (Γ , `Bool) (`Type ℓ))
    (pt : Value Γ (subT ⟦ P ⟧ `true))
    (pf : Value Γ (subT ⟦ P ⟧ `false))
    (b : Neutral Γ `Bool) → Neutral Γ (subT ⟦ P ⟧ (`neut b))
  `proj₁ : ∀{A B} → Neutral Γ (`Σ A B) → Neutral Γ A
  `proj₂ : ∀{A B} (ab : Neutral Γ (`Σ A B)) → Neutral Γ (subT B (`neut (`proj₁ ab)))
  _`$_ : ∀{A B} (f : Neutral Γ (`Π A B)) (a : Value Γ A) → Neutral Γ (subT B a)
  `des : ∀{ℓ} {D : Value Γ (`Desc ℓ)} → Neutral Γ (`μ D) → Neutral Γ (⟦ D ⟧ᵈ (`μ D))

----------------------------------------------------------------------

⟦ `Π A B ⟧ = `Π ⟦ A ⟧ ⟦ B ⟧
⟦ `Σ A B ⟧ = `Σ ⟦ A ⟧ ⟦ B ⟧
⟦ `⊥ ⟧ = `⊥
⟦ `⊤ ⟧ = `⊤
⟦ `Bool ⟧ = `Bool
⟦ `μ D ⟧ = `μ D
⟦ `Type {zero} ⟧ = `⊥
⟦ `Type {suc ℓ} ⟧ = `Type ℓ
⟦ `⟦ A ⟧ ⟧ = ⟦ A ⟧
⟦ `Desc {ℓ} ⟧ = `Desc ℓ
⟦ `⟦ D ⟧ᵈ X ⟧ = ⟦ D ⟧ᵈ ⟦ X ⟧
⟦ `neut A ⟧ = `⟦ A ⟧

----------------------------------------------------------------------

⟦ `⊤ᵈ ⟧ᵈ X = `⊤
⟦ `Xᵈ ⟧ᵈ X = X
⟦ `Πᵈ A D ⟧ᵈ X = `Π ⟦ A ⟧ (⟦ D ⟧ᵈ (wknT X))
⟦ `Σᵈ A D ⟧ᵈ X = `Σ ⟦ A ⟧ (⟦ D ⟧ᵈ (wknT X))
⟦ `neut D ⟧ᵈ X = `⟦ D ⟧ᵈ X

----------------------------------------------------------------------

elim⊥ : ∀{Γ A} → Value Γ `⊥ → Value Γ A
elim⊥ (`neut bot) = `neut (`elim⊥ bot)

----------------------------------------------------------------------

if_then_else_ : ∀{Γ C} (b : Value Γ `Bool) (c₁ c₂ : Value Γ C) → Value Γ C
if `true then c₁ else c₂ = c₁
if `false then c₁ else c₂ = c₂
if `neut b then c₁ else c₂ = `neut (`if b `then c₁ `else c₂)

elimBool : ∀{Γ ℓ} (P : Value (Γ , `Bool) (`Type ℓ))
  (pt : Value Γ (subT ⟦ P ⟧ `true))
  (pf : Value Γ (subT ⟦ P ⟧ `false))
  (b : Value Γ `Bool)
  → Value Γ (subT ⟦ P ⟧ b)
elimBool P pt pf `true = pt
elimBool P pt pf `false = pf
elimBool P pt pf (`neut b) = `neut (`elimBool P pt pf b)

----------------------------------------------------------------------

proj₁ : ∀{Γ A B} → Value Γ (`Σ A B) → Value Γ A
proj₁ (a `, b) = a
proj₁ (`neut ab) = `neut (`proj₁ ab)

proj₂ : ∀{Γ A B} (ab : Value Γ (`Σ A B)) → Value Γ (subT B (proj₁ ab))
proj₂ (a `, b) = b
proj₂ (`neut ab) = `neut (`proj₂ ab)

----------------------------------------------------------------------

des : ∀{Γ ℓ} {D : Value Γ (`Desc ℓ)} → Value Γ (`μ D) → Value Γ (⟦ D ⟧ᵈ (`μ D))
des (`con x) = x
des (`neut x) = `neut (`des x)

----------------------------------------------------------------------

_$_ : ∀{Γ A B} → Value Γ (`Π A B) → (a : Value Γ A) → Value Γ (subT B a)
`λ b $ a = subV b a
`neut f $ a = `neut (f `$ a)

----------------------------------------------------------------------

data Term (Γ : Context) : Type Γ → Set
eval : ∀{Γ A} → Term Γ A → Value Γ A

data Term Γ where
  {- Type introduction -}
  `⊥ `⊤ `Bool `Type : ∀{ℓ} → Term Γ (`Type ℓ)
  `Π `Σ : ∀{ℓ} (A : Term Γ (`Type ℓ)) (B : Term (Γ , ⟦ eval A ⟧) (`Type ℓ)) → Term Γ (`Type ℓ)
  `μ : ∀{ℓ} → Term Γ (`Desc ℓ) → Term Γ (`Type ℓ)
  `⟦_⟧ : ∀{ℓ} → Term Γ (`Type ℓ) → Term Γ (`Type (suc ℓ))
  `⟦_⟧ᵈ : ∀{ℓ} → Term Γ (`Desc ℓ) → Term Γ (`Type ℓ) → Term Γ (`Type ℓ)

  {- Desc introduction -}
  `⊤ᵈ `Xᵈ : ∀{ℓ} → Term Γ (`Desc ℓ)
  `Πᵈ `Σᵈ : ∀{ℓ}
    (A : Term Γ (`Type ℓ))
    (D : Term (Γ , ⟦ eval A ⟧) (`Desc (suc ℓ)))
    → Term Γ (`Desc (suc ℓ))

  {- Value introduction -}
  `tt : Term Γ `⊤
  `true `false : Term Γ `Bool
  _`,_ : ∀{A B}
    (a : Term Γ A) (b : Term Γ (subT B (eval a)))
    → Term Γ (`Σ A B)
  `λ : ∀{A B}
    (b : Term (Γ , A) B)
    → Term Γ (`Π A B)
  `con : ∀{ℓ} {D : Value Γ (`Desc ℓ)} → Term Γ (⟦ D ⟧ᵈ (`μ D)) → Term Γ (`μ D)
  
  {- Value elimination -}
  `var : ∀{A} → Var Γ A → Term Γ A
  `if_`then_`else_ : ∀{C}
    (b : Term Γ `Bool)
    (c₁ c₂ : Term Γ C)
    → Term Γ C
  _`$_ : ∀{A B} (f : Term Γ (`Π A B)) (a : Term Γ A) → Term Γ (subT B (eval a))
  `proj₁ : ∀{A B} → Term Γ (`Σ A B) → Term Γ A
  `proj₂ : ∀{A B} (ab : Term Γ (`Σ A B)) → Term Γ (subT B (proj₁ (eval ab)))
  `elim⊥ : ∀{A} → Term Γ `⊥ → Term Γ A
  `elimBool : ∀{ℓ} (P : Term (Γ , `Bool) (`Type ℓ))
    (pt : Term Γ (subT ⟦ eval P ⟧ `true))
    (pf : Term Γ (subT ⟦ eval P ⟧ `false))
    (b : Term Γ `Bool)
    → Term Γ (subT ⟦ eval P ⟧ (eval b))
  `des : ∀{ℓ} {D : Value Γ (`Desc ℓ)} → Term Γ (`μ D) → Term Γ (⟦ D ⟧ᵈ (`μ D))

----------------------------------------------------------------------

{- Type introduction -}
eval `⊥ = `⊥
eval `⊤ = `⊤
eval `Bool = `Bool
eval `Type = `Type
eval (`Π A B) = `Π (eval A) (eval B)
eval (`Σ A B) = `Σ (eval A) (eval B)
eval (`μ D) = `μ (eval D)
eval `⟦ A ⟧ = `⟦ eval A ⟧
eval (`⟦ D ⟧ᵈ X) = `⟦ eval D ⟧ᵈ (eval X)

{- Desc introduction -}
eval `⊤ᵈ = `⊤ᵈ
eval `Xᵈ = `Xᵈ
eval (`Πᵈ A D) = `Πᵈ (eval A) (eval D)
eval (`Σᵈ A D) = `Σᵈ (eval A) (eval D)

{- Value introduction -}
eval `tt = `tt
eval `true = `true
eval `false = `false
eval (a `, b) = eval a `, eval b
eval (`λ b) = `λ (eval b)
eval (`con x) = `con (eval x)

{- Value elimination -}
eval (`var i) = `neut (`var i)
eval (`if b `then c₁ `else c₂) = if eval b then eval c₁ else eval c₂
eval (f `$ a) = eval f $ eval a
eval (`proj₁ ab) = proj₁ (eval ab)
eval (`proj₂ ab) = proj₂ (eval ab)
eval (`elim⊥ bot) = elim⊥ (eval bot)
eval (`elimBool P pt pf b) = elimBool (eval P) (eval pt) (eval pf) (eval b)
eval (`des x) = des (eval x)

----------------------------------------------------------------------

