{-# OPTIONS --type-in-type #-}
open import Data.Unit
open import Data.Product hiding ( curry ; uncurry )
open import Data.List hiding ( concat )
open import Data.String
open import Relation.Binary.PropositionalEquality
module Spire.Examples.PropositionalDesc where

----------------------------------------------------------------------

elimEq : (A : Set) (x : A) (P : (y : A) → x ≡ y → Set)
  → P x refl
  → (y : A) (p : x ≡ y) → P y p
elimEq A .x P prefl x refl = prefl

----------------------------------------------------------------------

Label : Set
Label = String

Enum : Set
Enum = List Label

data Tag : Enum → Set where
  here : ∀{l E} → Tag (l ∷ E)
  there : ∀{l E} → Tag E → Tag (l ∷ E)

Cases : (E : Enum) (P : Tag E → Set) → Set
Cases [] P = ⊤
Cases (l ∷ E) P = P here × Cases E λ t → P (there t)

case : (E : Enum) (P : Tag E → Set) (cs : Cases E P) (t : Tag E) → P t
case (l ∷ E) P (c , cs) here = c
case (l ∷ E) P (c , cs) (there t) = case E (λ t → P (there t)) cs t

----------------------------------------------------------------------

data Desc (I : Set) : Set₁ where
  `End : (i : I) → Desc I
  `Rec : (i : I) (D : Desc I) → Desc I
  `Arg : (A : Set) (B : A → Desc I) → Desc I
  `RecFun : (A : Set) (B : A → I) (D : Desc I) → Desc I

ISet : Set → Set₁
ISet I = I → Set

El : (I : Set) (D : Desc I) (X : ISet I) → ISet I
El I (`End j) X i = j ≡ i
El I (`Rec j D) X i = X j × El I D X i
El I (`Arg A B) X i = Σ A (λ a → El I (B a) X i)
El I (`RecFun A B D) X i = ((a : A) → X (B a)) × El I D X i

data μ (I : Set) (D : Desc I) (i : I) : Set where
  con : El I D (μ I D) i → μ I D i

All : (I : Set) (D : Desc I) (X : ISet I) (P : (i : I) → X i → Set) (i : I) (xs : El I D X i) → Set
All I (`End j) X P i q = ⊤
All I (`Rec j D) X P i (x , xs) = P j x × All I D X P i xs
All I (`Arg A B) X P i (a , b) = All I (B a) X P i b
All I (`RecFun A B D) X P i (f , xs) = ((a : A) → P (B a) (f a)) × All I D X P i xs

caseD : (E : Enum) (I : Set) (cs : Cases E (λ _ → Desc I)) (t : Tag E) → Desc I
caseD E I cs t = case E (λ _ → Desc I) cs t

----------------------------------------------------------------------

ind :
  (I : Set)
  (D : Desc I)
  (P : (i : I) → μ I D i → Set)
  (pcon : (i : I) (xs : El I D (μ I D) i) → All I D (μ I D) P i xs → P i (con xs))
  (i : I)
  (x : μ I D i)
  → P i x

hyps :
  (I : Set)
  (D₁ : Desc I)
  (P : (i : I) → μ I D₁ i → Set)
  (pcon : (i : I) (xs : El I D₁ (μ I D₁) i) → All I D₁ (μ I D₁) P i xs → P i (con xs))
  (D₂ : Desc I)
  (i : I)
  (xs : El I D₂ (μ I D₁) i)
  → All I D₂ (μ I D₁) P i xs

ind I D P pcon i (con xs) = pcon i xs (hyps I D P pcon D i xs)

hyps I D P pcon (`End j) i q = tt
hyps I D P pcon (`Rec j A) i (x , xs) = ind I D P pcon j x , hyps I D P pcon A i xs
hyps I D P pcon (`Arg A B) i (a , b) = hyps I D P pcon (B a) i b
hyps I D P pcon (`RecFun A B E) i (f , xs) = (λ a → ind I D P pcon (B a) (f a)) , hyps I D P pcon E i xs

----------------------------------------------------------------------

Uncurried : (I : Set) (D : Desc I) (X : I → Set) → Set
Uncurried I D X = {i : I} → El I D X i → X i

Curried : (I : Set) (D : Desc I) (X : I → Set) → Set
Curried I (`End i) X = X i
Curried I (`Rec j D) X = (x : X j) → Curried I D X
Curried I (`Arg A B) X = (a : A) → Curried I (B a) X
Curried I (`RecFun A B D) X = ((a : A) → X (B a)) → Curried I D X

curry : (I : Set) (D : Desc I) (X : I → Set)
  (cn : Uncurried I D X) → Curried I D X
curry I (`End i) X cn = cn refl
curry I (`Rec i D) X cn = λ x → curry I D X (λ xs → cn (x , xs))
curry I (`Arg A B) X cn = λ a → curry I (B a) X (λ xs → cn (a , xs))
curry I (`RecFun A B D) X cn = λ f → curry I D X (λ xs → cn (f , xs))

uncurry : (I : Set) (D : Desc I) (X : I → Set)
  (cn : Curried I D X) → Uncurried I D X
uncurry I (`End i) X cn refl = cn
uncurry I (`Rec i D) X cn (x , xs) = uncurry I D X (cn x) xs
uncurry I (`Arg A B) X cn (a , xs) = uncurry I (B a) X (cn a) xs
uncurry I (`RecFun A B D) X cn (f , xs) = uncurry I D X (cn f) xs

con2 : (I : Set) (D : Desc I) → Curried I D (μ I D)
con2 I D = curry I D (μ I D) con

----------------------------------------------------------------------

module Sugared where

  data ℕT : Set where `zero `suc : ℕT
  data VecT : Set where `nil `cons : VecT

  ℕD : Desc ⊤
  ℕD = `Arg ℕT λ
    { `zero → `End tt
    ; `suc → `Rec tt (`End tt)
    }

  ℕ : ⊤ → Set
  ℕ = μ ⊤ ℕD

  zero : ℕ tt
  zero = con (`zero , refl)

  suc : ℕ tt → ℕ tt
  suc n = con (`suc , n , refl)

  VecD : (A : Set) → Desc (ℕ tt)
  VecD A = `Arg VecT λ
    { `nil  → `End zero
    ; `cons → `Arg (ℕ tt) λ n → `Arg A λ _ → `Rec n (`End (suc n))
    }

  Vec : (A : Set) (n : ℕ tt) → Set
  Vec A n = μ (ℕ tt) (VecD A) n

  nil : (A : Set) → Vec A zero
  nil A = con (`nil , refl)

  cons : (A : Set) (n : ℕ tt) (x : A) (xs : Vec A n) → Vec A (suc n)
  cons A n x xs = con (`cons , n , x , xs , refl)

----------------------------------------------------------------------

  add : ℕ tt → ℕ tt → ℕ tt
  add = ind ⊤ ℕD (λ _ _ → ℕ tt → ℕ tt)
    (λ
      { tt (`zero , q) tt n → n
      ; tt (`suc , m , q) (ih , tt) n → suc (ih n)
      }
    )
    tt

  mult : ℕ tt → ℕ tt → ℕ tt
  mult = ind ⊤ ℕD (λ _ _ → ℕ tt → ℕ tt)
    (λ
      { tt (`zero , q) tt n → zero
      ; tt (`suc , m , q) (ih , tt) n → add n (ih n)
      }
    )
    tt

  append : (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n) 
  append A = ind (ℕ tt) (VecD A) (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n))
    (λ
      { .(con (`zero , refl)) (`nil , refl) ih n ys → ys
      ; .(con (`suc , m , refl)) (`cons , m , x , xs , refl) (ih , tt) n ys → cons A (add m n) x (ih n ys)
      }
    )

  concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Vec A (mult n m)
  concat A m = ind (ℕ tt) (VecD (Vec A m)) (λ n xss → Vec A (mult n m))
    (λ
      { .(con (`zero , refl)) (`nil , refl) tt → nil A
      ; .(con (`suc , n , refl)) (`cons , n , xs , xss , refl) (ih , tt) → append A m xs (mult n m) ih
      }
    )

----------------------------------------------------------------------

module Desugared where

  ℕT : Enum
  ℕT = "zero" ∷ "suc" ∷ []
  
  VecT : Enum
  VecT = "nil" ∷ "cons" ∷ []
  
  ℕC : Tag ℕT → Desc ⊤
  ℕC = caseD ℕT ⊤
    ( `End tt
    , `Rec tt (`End tt)
    , tt
    )
  
  ℕD : Desc ⊤
  ℕD = `Arg (Tag ℕT) ℕC
  
  ℕ : ⊤ → Set
  ℕ = μ ⊤ ℕD
  
  zero : ℕ tt
  zero = con (here , refl)
  
  suc : ℕ tt → ℕ tt
  suc n = con (there here , n , refl)
  
  zero2 : ℕ tt
  zero2 = con2 ⊤ ℕD here

  suc2 : ℕ tt → ℕ tt
  suc2 = con2 ⊤ ℕD (there here)

  VecC : (A : Set) → Tag VecT → Desc (ℕ tt)
  VecC A = caseD VecT (ℕ tt)
    ( `End zero
    , `Arg (ℕ tt) (λ n → `Arg A λ _ → `Rec n (`End (suc n)))
    , tt
    )
  
  VecD : (A : Set) → Desc (ℕ tt)
  VecD A = `Arg (Tag VecT) (VecC A)
  
  Vec : (A : Set) (n : ℕ tt) → Set
  Vec A n = μ (ℕ tt) (VecD A) n
  
  nil : (A : Set) → Vec A zero
  nil A = con (here , refl)
  
  cons : (A : Set) (n : ℕ tt) (x : A) (xs : Vec A n) → Vec A (suc n)
  cons A n x xs = con (there here , n , x , xs , refl)
 
  nil2 : (A : Set) → Vec A zero
  nil2 A = con2 (ℕ tt) (VecD A) here

  cons2 : (A : Set) (n : ℕ tt) (x : A) (xs : Vec A n) → Vec A (suc n)
  cons2 A = con2 (ℕ tt) (VecD A) (there here)

----------------------------------------------------------------------

  module Induction where

    add : ℕ tt → ℕ tt → ℕ tt
    add = ind ⊤ ℕD (λ _ _ → ℕ tt → ℕ tt)
      (λ u t,c → case ℕT
        (λ t → (c : El ⊤ (ℕC t) ℕ u)
               (ih : All ⊤ ℕD ℕ (λ u n → ℕ u → ℕ u) u (t , c))
               → ℕ u → ℕ u
        )
        ( (λ q ih n → n)
        , (λ m,q ih,tt n → suc (proj₁ ih,tt n))
        , tt
        )
        (proj₁ t,c)
        (proj₂ t,c)
      )
      tt
    
    mult : ℕ tt → ℕ tt → ℕ tt
    mult = ind ⊤ ℕD (λ _ _ → ℕ tt → ℕ tt)
      (λ u t,c → case ℕT
        (λ t → (c : El ⊤ (ℕC t) ℕ u)
               (ih : All ⊤ ℕD ℕ (λ u n → ℕ u → ℕ u) u (t , c))
               → ℕ u → ℕ u
        )
        ( (λ q ih n → zero)
        , (λ m,q ih,tt n → add n (proj₁ ih,tt n))
        , tt
        )
        (proj₁ t,c)
        (proj₂ t,c)
      )
      tt
    
    append : (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n) 
    append A = ind (ℕ tt) (VecD A) (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n))
      (λ m t,c → case VecT
        (λ t → (c : El (ℕ tt) (VecC A t) (Vec A) m)
               (ih : All (ℕ tt) (VecD A) (Vec A) (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)) m (t , c))
               (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)
        )
        ( (λ q ih n ys → subst (λ m → Vec A (add m n)) q ys)
        , (λ m',x,xs,q ih,tt n ys →
            let m' = proj₁ m',x,xs,q
                x = proj₁ (proj₂ m',x,xs,q)
                q = proj₂ (proj₂ (proj₂ m',x,xs,q))
                ih = proj₁ ih,tt
            in
            subst (λ m → Vec A (add m n)) q (cons A (add m' n) x (ih n ys))
          )
        , tt
        )
        (proj₁ t,c)
        (proj₂ t,c)
      )
    
    concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Vec A (mult n m)
    concat A m = ind (ℕ tt) (VecD (Vec A m)) (λ n xss → Vec A (mult n m))
      (λ n t,c → case VecT
        (λ t → (c : El (ℕ tt) (VecC (Vec A m) t) (Vec (Vec A m)) n)
               (ih : All (ℕ tt) (VecD (Vec A m)) (Vec (Vec A m)) (λ n xss → Vec A (mult n m)) n (t , c))
               → Vec A (mult n m)
        )
        ( (λ q ih → subst (λ n → Vec A (mult n m)) q (nil A))
        , (λ n',xs,xss,q ih,tt →
            let n' = proj₁ n',xs,xss,q
                xs = proj₁ (proj₂ n',xs,xss,q)
                q = proj₂ (proj₂ (proj₂ n',xs,xss,q))
                ih = proj₁ ih,tt
            in
            subst (λ n → Vec A (mult n m)) q (append A m xs (mult n' m) ih)
          )
        , tt
        )
        (proj₁ t,c)
        (proj₂ t,c)
      )

----------------------------------------------------------------------

  module Eliminator where

    elimℕ : (P : (ℕ tt) → Set)
      (pzero : P zero)
      (psuc : (m : ℕ tt) → P m → P (suc m))
      (n : ℕ tt)
      → P n
    elimℕ P pzero psuc = ind ⊤ ℕD (λ u n → P n)
      (λ u t,c → case ℕT
        (λ t → (c : El ⊤ (ℕC t) ℕ u)
               (ih : All ⊤ ℕD ℕ (λ u n → P n) u (t , c))
               → P (con (t , c))
        )
        ( (λ q ih →
            elimEq ⊤ tt (λ u q → P (con (here , q)))
              pzero
              u q
          )
        , (λ n,q ih,tt →
            elimEq ⊤ tt (λ u q → P (con (there here , proj₁ n,q , q)))
              (psuc (proj₁ n,q) (proj₁ ih,tt))
              u (proj₂ n,q)
          )
        , tt
        )
        (proj₁ t,c)
        (proj₂ t,c)
      )
      tt

    elimVec : (A : Set) (P : (n : ℕ tt) → Vec A n → Set)
      (pnil : P zero (nil A))
      (pcons : (n : ℕ tt) (a : A) (xs : Vec A n) → P n xs → P (suc n) (cons A n a xs))
      (n : ℕ tt)
      (xs : Vec A n)
      → P n xs
    elimVec A P pnil pcons = ind (ℕ tt) (VecD A) (λ n xs → P n xs)
      (λ n t,c → case VecT
        (λ t → (c : El (ℕ tt) (VecC A t) (Vec A) n)
               (ih : All (ℕ tt) (VecD A) (Vec A) (λ n xs → P n xs) n (t , c))
               → P n (con (t , c))
        )
        ( (λ q ih →
            elimEq (ℕ tt) zero (λ n q → P n (con (here , q)))
              pnil
              n q
          )
        , (λ n',x,xs,q ih,tt →
            let n' = proj₁ n',x,xs,q
                x = proj₁ (proj₂ n',x,xs,q)
                xs = proj₁ (proj₂ (proj₂ n',x,xs,q))
                q = proj₂ (proj₂ (proj₂ n',x,xs,q))
                ih = proj₁ ih,tt
            in
            elimEq (ℕ tt) (suc n') (λ n q → P n (con (there here , n' , x , xs , q)))
              (pcons n' x xs ih )
              n q
          )
        , tt
        )
        (proj₁ t,c)
        (proj₂ t,c)
      )

----------------------------------------------------------------------

    add : ℕ tt → ℕ tt → ℕ tt
    add = elimℕ (λ _ → ℕ tt → ℕ tt)
      (λ n → n)
      (λ m ih n → suc (ih n))
  
    mult : ℕ tt → ℕ tt → ℕ tt
    mult = elimℕ (λ _ → ℕ tt → ℕ tt)
      (λ n → zero)
      (λ m ih n → add n (ih n))
  
    append : (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)
    append A = elimVec A (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n))
      (λ n ys → ys)
      (λ m x xs ih n ys → cons A (add m n) x (ih n ys))
  
    concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Vec A (mult n m)
    concat A m = elimVec (Vec A m) (λ n xss → Vec A (mult n m))
      (nil A)
      (λ n xs xss ih → append A m xs (mult n m) ih)
    
----------------------------------------------------------------------
