module Spire.Examples.Standard where

----------------------------------------------------------------------

data ℕ : Set where
  zero : ℕ
  suc : (n : ℕ) → ℕ

data Vec (A : Set) : ℕ → Set where
  nil : Vec A zero
  cons : (n : ℕ) (a : A) (xs : Vec A n) → Vec A (suc n)

----------------------------------------------------------------------

elimℕ : (P : ℕ → Set)
  (pzero : P zero)
  (psuc : (m : ℕ) → P m → P (suc m))
  (n : ℕ)
  → P n
elimℕ P pzero psuc zero = pzero
elimℕ P pzero psuc (suc n) = psuc n (elimℕ P pzero psuc n)

elimVec : (A : Set) (P : (n : ℕ) → Vec A n → Set)
  (pnil : P zero nil)
  (pcons : (n : ℕ) (a : A) (xs : Vec A n) → P n xs → P (suc n) (cons n a xs))
  (n : ℕ)
  (xs : Vec A n)
  → P n xs
elimVec A P pnil pcons .zero nil = pnil
elimVec A P pnil pcons .(suc n) (cons n a xs) = pcons n a xs (elimVec A P pnil pcons n xs)

----------------------------------------------------------------------

module PatternMatching where

  add : ℕ → ℕ → ℕ
  add zero n = n
  add (suc m) n = suc (add m n)
  
  mult : ℕ → ℕ → ℕ
  mult zero n = zero
  mult (suc m) n = add n (mult m n)

  append : (A : Set) (m : ℕ) (xs : Vec A m) (n : ℕ) (ys : Vec A n) → Vec A (add m n)
  append A .zero nil n ys = ys
  append A .(suc m) (cons m x xs) n ys = cons (add m n) x (append A m xs n ys) 
  
  concat : (A : Set) (m n : ℕ) (xss : Vec (Vec A m) n) → Vec A (mult n m)
  concat A m .zero nil = nil
  concat A m .(suc n) (cons n xs xss) = append A m xs (mult n m) (concat A m n xss)

----------------------------------------------------------------------

module Eliminator where

  add : ℕ → ℕ → ℕ
  add = elimℕ (λ _ → ℕ → ℕ)
    (λ n → n)
    (λ m ih n → suc (ih n))

  mult : ℕ → ℕ → ℕ
  mult = elimℕ (λ _ → ℕ → ℕ)
    (λ n → zero)
    (λ m ih n → add n (ih n))

  append : (A : Set) (m : ℕ) (xs : Vec A m) (n : ℕ) (ys : Vec A n) → Vec A (add m n)
  append A = elimVec A (λ m xs → (n : ℕ) (ys : Vec A n) → Vec A (add m n))
    (λ n ys → ys)
    (λ m x xs ih n ys → cons (add m n) x (ih n ys))

  concat : (A : Set) (m n : ℕ) (xss : Vec (Vec A m) n) → Vec A (mult n m)
  concat A m = elimVec (Vec A m) (λ n xss → Vec A (mult n m))
    nil
    (λ n xs xss ih → append A m xs (mult n m) ih)

----------------------------------------------------------------------
