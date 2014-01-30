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

UncurriedCases : (E : Enum) (P : Tag E → Set) (X : Set)
  → Set
UncurriedCases E P X = Cases E P → X

CurriedCases : (E : Enum) (P : Tag E → Set) (X : Set)
  → Set
CurriedCases [] P X = X
CurriedCases (l ∷ E) P X = P here → CurriedCases E (λ t → P (there t)) X

curryCases : (E : Enum) (P : Tag E → Set) (X : Set)
  (f : UncurriedCases E P X) → CurriedCases E P X
curryCases [] P X f = f tt
curryCases (l ∷ E) P X f = λ c → curryCases E (λ t → P (there t)) X (λ cs → f (c , cs))

uncurryCases : (E : Enum) (P : Tag E → Set) (X : Set)
  (f : CurriedCases E P X) → UncurriedCases E P X
uncurryCases [] P X x tt = x
uncurryCases (l ∷ E) P X f (c , cs) = uncurryCases E (λ t → P (there t)) X (f c) cs

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

All : (I : Set) (D : Desc I) (X : ISet I) (P : (i : I) → X i → Set) (i : I) (xs : El I D X i) → Set
All I (`End j) X P i q = ⊤
All I (`Rec j D) X P i (x , xs) = P j x × All I D X P i xs
All I (`Arg A B) X P i (a , b) = All I (B a) X P i b
All I (`RecFun A B D) X P i (f , xs) = ((a : A) → P (B a) (f a)) × All I D X P i xs

caseD : (E : Enum) (I : Set) (cs : Cases E (λ _ → Desc I)) (t : Tag E) → Desc I
caseD E I cs t = case E (λ _ → Desc I) cs t

----------------------------------------------------------------------

TagDesc : (I : Set) → Set
TagDesc I = Σ Enum (λ E → Cases E (λ _ → Desc I))

toCase : (I : Set) (E,cs : TagDesc I) → Tag (proj₁ E,cs) → Desc I
toCase I (E , cs) = case E (λ _ → Desc I) cs

toDesc : (I : Set) → TagDesc I → Desc I
toDesc I (E , cs) = `Arg (Tag E) (toCase I (E , cs))

----------------------------------------------------------------------

UncurriedEl : (I : Set) (D : Desc I) (X : ISet I) → Set
UncurriedEl I D X = {i : I} → El I D X i → X i

CurriedEl : (I : Set) (D : Desc I) (X : ISet I) → Set
CurriedEl I (`End i) X = X i
CurriedEl I (`Rec j D) X = (x : X j) → CurriedEl I D X
CurriedEl I (`Arg A B) X = (a : A) → CurriedEl I (B a) X
CurriedEl I (`RecFun A B D) X = ((a : A) → X (B a)) → CurriedEl I D X

curryEl : (I : Set) (D : Desc I) (X : ISet I)
  (cn : UncurriedEl I D X) → CurriedEl I D X
curryEl I (`End i) X cn = cn refl
curryEl I (`Rec i D) X cn = λ x → curryEl I D X (λ xs → cn (x , xs))
curryEl I (`Arg A B) X cn = λ a → curryEl I (B a) X (λ xs → cn (a , xs))
curryEl I (`RecFun A B D) X cn = λ f → curryEl I D X (λ xs → cn (f , xs))

uncurryEl : (I : Set) (D : Desc I) (X : ISet I)
  (cn : CurriedEl I D X) → UncurriedEl I D X
uncurryEl I (`End i) X cn refl = cn
uncurryEl I (`Rec i D) X cn (x , xs) = uncurryEl I D X (cn x) xs
uncurryEl I (`Arg A B) X cn (a , xs) = uncurryEl I (B a) X (cn a) xs
uncurryEl I (`RecFun A B D) X cn (f , xs) = uncurryEl I D X (cn f) xs

data μ (I : Set) (D : Desc I) : I → Set where
  con : UncurriedEl I D (μ I D)

con2 : (I : Set) (D : Desc I) → CurriedEl I D (μ I D)
con2 I D = curryEl I D (μ I D) con

----------------------------------------------------------------------

UncurriedAll : (I : Set) (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : {i : I} → El I D X i → X i)
  → Set
UncurriedAll I D X P cn =
  (i : I) (xs : El I D X i) → All I D X P i xs → P i (cn xs)

CurriedAll : (I : Set) (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedEl I D X)
  → Set
CurriedAll I (`End i) X P cn =
  P i (cn refl)
CurriedAll I (`Rec i D) X P cn =
  (x : X i) → P i x → CurriedAll I D X P (λ xs → cn (x , xs))
CurriedAll I (`Arg A B) X P cn =
  (a : A) → CurriedAll I (B a) X P (λ xs → cn (a , xs))
CurriedAll I (`RecFun A B D) X P cn =
  (f : (a : A) → X (B a)) (ihf : (a : A) → P (B a) (f a)) → CurriedAll I D X P (λ xs → cn (f , xs))

curryAll : (I : Set) (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedEl I D X)
  (pf : UncurriedAll I D X P cn)
  → CurriedAll I D X P cn
curryAll I (`End i) X P cn pf =
  pf i refl tt
curryAll I (`Rec i D) X P cn pf =
  λ x ih → curryAll I D X P (λ xs → cn (x , xs)) (λ i xs ihs → pf i (x , xs) (ih , ihs))
curryAll I (`Arg A B) X P cn pf =
  λ a → curryAll I (B a) X P (λ xs → cn (a , xs)) (λ i xs ihs → pf i (a , xs) ihs)
curryAll I (`RecFun A B D) X P cn pf =
  λ f ihf → curryAll I D X P (λ xs → cn (f , xs)) (λ i xs ihs → pf i (f , xs) (ihf , ihs))

uncurryAll : (I : Set) (D : Desc I) (X : ISet I)
  (P : (i : I) → X i → Set)
  (cn : UncurriedEl I D X)
  (pf : CurriedAll I D X P cn)
  → UncurriedAll I D X P cn
uncurryAll I (`End .i) X P cn pf i refl tt =
  pf
uncurryAll I (`Rec j D) X P cn pf i (x , xs) (ih , ihs) =
  uncurryAll I D X P (λ ys → cn (x , ys)) (pf x ih) i xs ihs
uncurryAll I (`Arg A B) X P cn pf i (a , xs) ihs =
  uncurryAll I (B a) X P (λ ys → cn (a , ys)) (pf a) i xs ihs
uncurryAll I (`RecFun A B D) X P cn pf i (f , xs) (ihf , ihs) =
  uncurryAll I D X P (λ ys → cn (f , ys)) (pf f ihf) i xs ihs

----------------------------------------------------------------------

ind :
  (I : Set)
  (D : Desc I)
  (P : (i : I) → μ I D i → Set)
  (pcon : UncurriedAll I D (μ I D) P con)
  (i : I)
  (x : μ I D i)
  → P i x

hyps :
  (I : Set)
  (D₁ : Desc I)
  (P : (i : I) → μ I D₁ i → Set)
  (pcon : UncurriedAll I D₁ (μ I D₁) P con)
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

ind2 :
  (I : Set)
  (D : Desc I)
  (P : (i : I) → μ I D i → Set)
  (pcon : CurriedAll I D (μ I D) P con)
  (i : I)
  (x : μ I D i)
  → P i x
ind2 I D P pcon i x = ind I D P (uncurryAll I D (μ I D) P con pcon) i x

elim :
  (I : Set)
  (TD : TagDesc I)
  → let
    D = toDesc I TD
    E = proj₁ TD
    Cs = toCase I TD
  in (P : (i : I) → μ I D i → Set)
  → let
    Q = λ t → CurriedAll I (Cs t) (μ I D) P (λ xs → con (t , xs))
    X = (i : I) (x : μ I D i) → P i x
  in UncurriedCases E Q X
elim I TD P cs i x =
  let
    D = toDesc I TD
    E = proj₁ TD
    Cs = toCase I TD
    p = case E (λ t → CurriedAll I (Cs t) (μ I D) P (λ xs → con (t , xs))) cs
  in ind2 I D P p i x

elim2 :
  (I : Set)
  (TD : TagDesc I)
  → let
    D = toDesc I TD
    E = proj₁ TD
    Cs = toCase I TD
  in (P : (i : I) → μ I D i → Set)
  → let
    Q = λ t → CurriedAll I (Cs t) (μ I D) P (λ xs → con (t , xs))
    X = (i : I) (x : μ I D i) → P i x
  in CurriedCases E Q X
elim2 I TD P =
  let
    D = toDesc I TD
    E = proj₁ TD
    Cs = toCase I TD
    Q = λ t → CurriedAll I (Cs t) (μ I D) P (λ xs → con (t , xs))
    X = (i : I) (x : μ I D i) → P i x
  in curryCases E Q X (elim I TD P)

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

  ℕTD : TagDesc ⊤
  ℕTD = ℕT
    , `End tt
    , `Rec tt (`End tt)
    , tt
  
  ℕC : Tag ℕT → Desc ⊤
  ℕC = toCase ⊤ ℕTD
  
  ℕD : Desc ⊤
  ℕD = toDesc ⊤ ℕTD
  
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

  VecTD : (A : Set) → TagDesc (ℕ tt)
  VecTD A = VecT
    , `End zero
    , `Arg (ℕ tt) (λ n → `Arg A λ _ → `Rec n (`End (suc n)))
    , tt

  VecC : (A : Set) → Tag VecT → Desc (ℕ tt)
  VecC A = toCase (ℕ tt) (VecTD A)
  
  VecD : (A : Set) → Desc (ℕ tt)
  VecD A = toDesc (ℕ tt) (VecTD A)
  
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

  module GenericEliminator where

    add : ℕ tt → ℕ tt → ℕ tt
    add = elim2 ⊤ ℕTD _
      (λ n → n)
      (λ m ih n → suc (ih n))
      tt

    mult : ℕ tt → ℕ tt → ℕ tt
    mult = elim2 ⊤ ℕTD _
      (λ n → zero)
      (λ m ih n → add n (ih n))
      tt

    append : (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)
    append A = elim2 (ℕ tt) (VecTD A) _
      (λ n ys → ys)
      (λ m x xs ih n ys → cons A (add m n) x (ih n ys))

    concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Vec A (mult n m)
    concat A m = elim2 (ℕ tt) (VecTD (Vec A m)) _
      (nil A)
      (λ n xs xss ih → append A m xs (mult n m) ih)

----------------------------------------------------------------------
