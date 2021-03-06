{-# OPTIONS --type-in-type #-}
open import Data.Unit
open import Data.Product
open import Data.List hiding ( concat )
open import Data.String
open import Relation.Binary.PropositionalEquality
module Spire.Examples.InferredPropositionalDesc where

----------------------------------------------------------------------

elimEq : {A : Set} (x : A) (P : (y : A) → x ≡ y → Set)
  → P x refl
  → (y : A) (p : x ≡ y) → P y p
elimEq .x P prefl x refl = prefl

----------------------------------------------------------------------

Label : Set
Label = String

Enum : Set
Enum = List Label

data Tag : Enum → Set where
  here : ∀{l E} → Tag (l ∷ E)
  there : ∀{l E} → Tag E → Tag (l ∷ E)

Cases : {E : Enum} (P : Tag E → Set) → Set
Cases {[]} P = ⊤
Cases {l ∷ E} P = P here × Cases λ t → P (there t)

case : {E : Enum} (P : Tag E → Set) (cs : Cases P) (t : Tag E) → P t
case {l ∷ E} P (c , cs) here = c
case {l ∷ E} P (c , cs) (there t) = case (λ t → P (there t)) cs t

----------------------------------------------------------------------

data Desc (I : Set) : Set₁ where
  `End : (i : I) → Desc I
  `Rec : (i : I) (D : Desc I) → Desc I
  `Arg : (A : Set) (B : A → Desc I) → Desc I
  `RecFun : (A : Set) (B : A → I) (D : Desc I) → Desc I

ISet : Set → Set₁
ISet I = I → Set

El : {I : Set} (D : Desc I) (X : ISet I) → ISet I
El (`End j) X i = j ≡ i
El (`Rec j D) X i = X j × El D X i
El (`Arg A B) X i = Σ A (λ a → El (B a) X i)
El (`RecFun A B D) X i = ((a : A) → X (B a)) × El D X i

data μ {I : Set} (D : Desc I) (i : I) : Set where
  con : El D (μ D) i → μ D i

All : {I : Set} (D : Desc I) {X : ISet I} (P : (i : I) → X i → Set) (i : I) (xs : El D X i) → Set
All (`End j) P i q = ⊤
All (`Rec j D) P i (x , xs) = P j x × All D P i xs
All (`Arg A B) P i (a , b) = All (B a) P i b
All (`RecFun A B D) P i (f , xs) = ((a : A) → P (B a) (f a)) × All D P i xs

caseD : (E : Enum) (I : Set) (cs : Cases (λ _ → Desc I)) (t : Tag E) → Desc I
caseD E I cs t = case (λ _ → Desc I) cs t

----------------------------------------------------------------------

ind :
  {I : Set}
  (D : Desc I)
  (P : (i : I) → μ D i → Set)
  (pcon : (i : I) (xs : El D (μ D) i) → All D P i xs → P i (con xs))
  {i : I}
  (x : μ D i)
  → P i x

hyps :
  {I : Set}
  (D₁ : Desc I)
  (P : (i : I) → μ D₁ i → Set)
  (pcon : (i : I) (xs : El D₁ (μ D₁) i) → All D₁ P i xs → P i (con xs))
  (D₂ : Desc I)
  {i : I}
  (xs : El D₂ (μ D₁) i)
  → All D₂ P i xs

ind D P pcon (con xs) = pcon _ xs (hyps D P pcon D xs)

hyps D P pcon (`End j) q = tt
hyps D P pcon (`Rec j A) (x , xs) = ind D P pcon x , hyps D P pcon A xs
hyps D P pcon (`Arg A B) (a , b) = hyps D P pcon (B a) b
hyps D P pcon (`RecFun A B E) (f , xs) = (λ a → ind D P pcon (f a)) , hyps D P pcon E xs

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
  ℕ = μ ℕD
  
  zero : ℕ tt
  zero = con (here , refl)
  
  suc : ℕ tt → ℕ tt
  suc n = con (there here , n , refl)
  
  VecC : (A : Set) → Tag VecT → Desc (ℕ tt)
  VecC A = caseD VecT (ℕ tt)
    ( `End zero
    , `Arg (ℕ tt) (λ n → `Arg A λ _ → `Rec n (`End (suc n)))
    , tt
    )
  
  VecD : (A : Set) → Desc (ℕ tt)
  VecD A = `Arg (Tag VecT) (VecC A)
  
  Vec : (A : Set) (n : ℕ tt) → Set
  Vec A n = μ (VecD A) n
  
  nil : (A : Set) → Vec A zero
  nil A = con (here , refl)
  
  cons : (A : Set) (n : ℕ tt) (x : A) (xs : Vec A n) → Vec A (suc n)
  cons A n x xs = con (there here , n , x , xs , refl)
 
----------------------------------------------------------------------

  module Induction where

    add : ℕ tt → ℕ tt → ℕ tt
    add = ind ℕD (λ _ _ → ℕ tt → ℕ tt)
      (λ u t,c → case
        (λ t → (c : El (ℕC t) ℕ u)
               (ih : All ℕD (λ u n → ℕ u → ℕ u) u (t , c))
               → ℕ u → ℕ u
        )
        ( (λ q ih n → n)
        , (λ m,q ih,tt n → suc (proj₁ ih,tt n))
        , tt
        )
        (proj₁ t,c)
        (proj₂ t,c)
      )
    
    mult : ℕ tt → ℕ tt → ℕ tt
    mult = ind ℕD (λ _ _ → ℕ tt → ℕ tt)
      (λ u t,c → case
        (λ t → (c : El (ℕC t) ℕ u)
               (ih : All ℕD (λ u n → ℕ u → ℕ u) u (t , c))
               → ℕ u → ℕ u
        )
        ( (λ q ih n → zero)
        , (λ m,q ih,tt n → add n (proj₁ ih,tt n))
        , tt
        )
        (proj₁ t,c)
        (proj₂ t,c)
      )
    
    append : (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n) 
    append A m = ind (VecD A) (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n))
      (λ m t,c → case
        (λ t → (c : El (VecC A t) (Vec A) m)
               (ih : All (VecD A) (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)) m (t , c))
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
    concat A m n = ind (VecD (Vec A m)) (λ n xss → Vec A (mult n m))
      (λ n t,c → case
        (λ t → (c : El (VecC (Vec A m) t) (Vec (Vec A m)) n)
               (ih : All (VecD (Vec A m)) (λ n xss → Vec A (mult n m)) n (t , c))
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
    elimℕ P pzero psuc = ind ℕD (λ u n → P n)
      (λ u t,c → case
        (λ t → (c : El (ℕC t) ℕ u)
               (ih : All ℕD (λ u n → P n) u (t , c))
               → P (con (t , c))
        )
        ( (λ q ih →
            elimEq tt (λ u q → P (con (here , q)))
              pzero
              u q
          )
        , (λ n,q ih,tt →
            elimEq tt (λ u q → P (con (there here , proj₁ n,q , q)))
              (psuc (proj₁ n,q) (proj₁ ih,tt))
              u (proj₂ n,q)
          )
        , tt
        )
        (proj₁ t,c)
        (proj₂ t,c)
      )

    elimVec : (A : Set) (P : (n : ℕ tt) → Vec A n → Set)
      (pnil : P zero (nil A))
      (pcons : (n : ℕ tt) (a : A) (xs : Vec A n) → P n xs → P (suc n) (cons A n a xs))
      (n : ℕ tt)
      (xs : Vec A n)
      → P n xs
    elimVec A P pnil pcons n = ind (VecD A) (λ n xs → P n xs)
      (λ n t,c → case
        (λ t → (c : El (VecC A t) (Vec A) n)
               (ih : All (VecD A) (λ n xs → P n xs) n (t , c))
               → P n (con (t , c))
        )
        ( (λ q ih →
            elimEq zero (λ n q → P n (con (here , q)))
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
            elimEq (suc n') (λ n q → P n (con (there here , n' , x , xs , q)))
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
