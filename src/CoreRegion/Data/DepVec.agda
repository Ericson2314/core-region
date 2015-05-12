module Data.DepVec where

open import Category.Applicative
open import Data.Nat
open import Data.Fin using (Fin; zero; suc)
open import Data.List as List using (List)
open import Data.Product as Prod using (∃; ∃₂; _×_; _,_)
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Types

infixr 5 _∷_

data DepVec {a} (A : ℕ → Set a) : ℕ → Set a where
  []  : DepVec A zero
  _∷_ : ∀ {n} (x : A n) (xs : DepVec A n) → DepVec A (suc n)

{-
infix 4 _∈_

data _∈_ {a} {A : ℕ → Set a} : {n : ℕ} → A n → DepVec A n → Set a where
  here  : ∀ {n} {x}   {xs : DepVec A n} → x ∈ x ∷ xs
  there : ∀ {n} {x y} {xs : DepVec A n} (x∈xs : x ∈ xs) → x ∈ y ∷ xs


infix 4 _[_]=_

data _[_]=_ {a} {A : Set a} :
            {n : ℕ} → DepVec A n → Fin n → A → Set a where
  here  : ∀ {n}     {x}   {xs : DepVec A n} → x ∷ xs [ zero ]= x
  there : ∀ {n} {i} {x y} {xs : DepVec A n}
          (xs[i]=x : xs [ i ]= x) → y ∷ xs [ suc i ]= x
-}

------------------------------------------------------------------------
-- Some operations

head : ∀ {a n} {A : ℕ → Set a} → DepVec A (1 + n) → A n
head (x ∷ xs) = x

tail : ∀ {a n} {A : ℕ → Set a} → DepVec A (1 + n) → DepVec A n
tail (x ∷ xs) = xs
{-
[_] : ∀ {a} {A : ℕ → Set a} → A → DepVec A 1
[ x ] = x ∷ []

infixr 5 _++_

_++_ : ∀ {a m n} {A : ℕ → Set a} → DepVec A m → DepVec A n → DepVec A (m + n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixl 4 _⊛_

_⊛_ : ∀ {a b n} {A : ℕ → Set a} {B : Set b} →
      DepVec (A → B) n → DepVec A n → DepVec B n
[]       ⊛ _        = []
(f ∷ fs) ⊛ (x ∷ xs) = f x ∷ (fs ⊛ xs)

replicate : ∀ {a n} {A : ℕ → Set a} → A → DepVec A n
replicate {n = zero}  x = []
replicate {n = suc n} x = x ∷ replicate x

applicative : ∀ {a n} → RawApplicative (λ (A : Set a) → DepVec A n)
applicative = record
  { pure = replicate
  ; _⊛_  = _⊛_
  }

map : ∀ {a b n} {A : ℕ → Set a} {B : Set b} →
      (A → B) → DepVec A n → DepVec B n
map f xs = replicate f ⊛ xs

zipWith : ∀ {a b c n} {A : ℕ → Set a} {B : Set b} {C : Set c} →
          (A → B → C) → DepVec A n → DepVec B n → DepVec C n
zipWith _⊕_ xs ys = replicate _⊕_ ⊛ xs ⊛ ys

zip : ∀ {a b n} {A : ℕ → Set a} {B : Set b} →
      DepVec A n → DepVec B n → DepVec (A × B) n
zip = zipWith _,_

unzip : ∀ {a b n} {A : ℕ → Set a} {B : Set b} →
        DepVec (A × B) n → DepVec A n × DepVec B n
unzip []              = [] , []
unzip ((x , y) ∷ xys) = Prod.map (_∷_ x) (_∷_ y) (unzip xys)

foldr : ∀ {a b} {A : ℕ → Set a} (B : ℕ → Set b) {m} →
        (∀ {n} → A → B n → B (suc n)) →
        B zero →
        DepVec A m → B m
foldr b _⊕_ n []       = n
foldr b _⊕_ n (x ∷ xs) = x ⊕ foldr b _⊕_ n xs

foldr₁ : ∀ {a} {A : ℕ → Set a} {m} →
         (A → A → A) → DepVec A (suc m) → A
foldr₁ _⊕_ (x ∷ [])     = x
foldr₁ _⊕_ (x ∷ y ∷ ys) = x ⊕ foldr₁ _⊕_ (y ∷ ys)

foldl : ∀ {a b} {A : ℕ → Set a} (B : ℕ → Set b) {m} →
        (∀ {n} → B n → A → B (suc n)) →
        B zero →
        DepVec A m → B m
foldl b _⊕_ n []       = n
foldl b _⊕_ n (x ∷ xs) = foldl (λ n → b (suc n)) _⊕_ (n ⊕ x) xs

foldl₁ : ∀ {a} {A : ℕ → Set a} {m} →
         (A → A → A) → DepVec A (suc m) → A
foldl₁ _⊕_ (x ∷ xs) = foldl _ _⊕_ x xs

concat : ∀ {a m n} {A : ℕ → Set a} →
         DepVec (DepVec A m) n → DepVec A (n * m)
concat []         = []
concat (xs ∷ xss) = xs ++ concat xss

splitAt : ∀ {a} {A : ℕ → Set a} m {n} (xs : DepVec A (m + n)) →
          ∃₂ λ (ys : DepVec A m) (zs : DepVec A n) → xs ≡ ys ++ zs
splitAt zero    xs                = ([] , xs , refl)
splitAt (suc m) (x ∷ xs)          with splitAt m xs
splitAt (suc m) (x ∷ .(ys ++ zs)) | (ys , zs , refl) =
  ((x ∷ ys) , zs , refl)

take : ∀ {a} {A : ℕ → Set a} m {n} → DepVec A (m + n) → DepVec A m
take m xs          with splitAt m xs
take m .(ys ++ zs) | (ys , zs , refl) = ys

drop : ∀ {a} {A : ℕ → Set a} m {n} → DepVec A (m + n) → DepVec A n
drop m xs          with splitAt m xs
drop m .(ys ++ zs) | (ys , zs , refl) = zs

group : ∀ {a} {A : ℕ → Set a} n k (xs : DepVec A (n * k)) →
        ∃ λ (xss : DepVec (DepVec A k) n) → xs ≡ concat xss
group zero    k []                  = ([] , refl)
group (suc n) k xs                  with splitAt k xs
group (suc n) k .(ys ++ zs)         | (ys , zs , refl) with group n k zs
group (suc n) k .(ys ++ concat zss) | (ys , ._ , refl) | (zss , refl) =
  ((ys ∷ zss) , refl)

-- Splits a vector into two "halves".

split : ∀ {a n} {A : ℕ → Set a} → DepVec A n → DepVec A ⌈ n /2⌉ × DepVec A ⌊ n /2⌋
split []           = ([]     , [])
split (x ∷ [])     = (x ∷ [] , [])
split (x ∷ y ∷ xs) = Prod.map (_∷_ x) (_∷_ y) (split xs)

reverse : ∀ {a n} {A : ℕ → Set a} → DepVec A n → DepVec A n
reverse {A = A} = foldl (DepVec A) (λ rev x → x ∷ rev) []

sum : ∀ {n} → DepVec ℕ n → ℕ
sum = foldr _ _+_ 0

toList : ∀ {a n} {A : ℕ → Set a} → DepVec A n → List A
toList []       = List.[]
toList (x ∷ xs) = List._∷_ x (toList xs)

fromList : ∀ {a} {A : ℕ → Set a} → (xs : List A) → DepVec A (List.length xs)
fromList List.[]         = []
fromList (List._∷_ x xs) = x ∷ fromList xs

-- Snoc.

infixl 5 _∷ʳ_

_∷ʳ_ : ∀ {a n} {A : ℕ → Set a} → DepVec A n → A → DepVec A (1 + n)
[]       ∷ʳ y = [ y ]
(x ∷ xs) ∷ʳ y = x ∷ (xs ∷ʳ y)

initLast : ∀ {a n} {A : ℕ → Set a} (xs : DepVec A (1 + n)) →
           ∃₂ λ (ys : DepVec A n) (y : A) → xs ≡ ys ∷ʳ y
initLast {n = zero}  (x ∷ [])         = ([] , x , refl)
initLast {n = suc n} (x ∷ xs)         with initLast xs
initLast {n = suc n} (x ∷ .(ys ∷ʳ y)) | (ys , y , refl) =
  ((x ∷ ys) , y , refl)

init : ∀ {a n} {A : ℕ → Set a} → DepVec A (1 + n) → DepVec A n
init xs         with initLast xs
init .(ys ∷ʳ y) | (ys , y , refl) = ys

last : ∀ {a n} {A : ℕ → Set a} → DepVec A (1 + n) → A
last xs         with initLast xs
last .(ys ∷ʳ y) | (ys , y , refl) = y

infixl 1 _>>=_

_>>=_ : ∀ {a b m n} {A : ℕ → Set a} {B : Set b} →
        DepVec A m → (A → DepVec B n) → DepVec B (m * n)
xs >>= f = concat (map f xs)

infixl 4 _⊛*_

_⊛*_ : ∀ {a b m n} {A : ℕ → Set a} {B : Set b} →
       DepVec (A → B) m → DepVec A n → DepVec B (m * n)
fs ⊛* xs = fs >>= λ f → map f xs

-- Interleaves the two vectors.

infixr 5 _⋎_

_⋎_ : ∀ {a m n} {A : ℕ → Set a} →
      DepVec A m → DepVec A n → DepVec A (m +⋎ n)
[]       ⋎ ys = ys
(x ∷ xs) ⋎ ys = x ∷ (ys ⋎ xs)

-- A lookup function.

lookup : ∀ {a n} {A : ℕ → Set a} → Fin n → DepVec A n → A
lookup zero    (x ∷ xs) = x
lookup (suc i) (x ∷ xs) = lookup i xs

-- An inverse of flip lookup.

tabulate : ∀ {n a} {A : ℕ → Set a} → (Fin n → A) → DepVec A n
tabulate {zero}  f = []
tabulate {suc n} f = f zero ∷ tabulate (f ∘ suc)

-- Update.

infixl 6 _[_]≔_

_[_]≔_ : ∀ {a n} {A : ℕ → Set a} → DepVec A n → Fin n → A → DepVec A n
[]       [ ()    ]≔ y
(x ∷ xs) [ zero  ]≔ y = y ∷ xs
(x ∷ xs) [ suc i ]≔ y = x ∷ xs [ i ]≔ y

-- Generates a vector containing all elements in Fin n. This function
-- is not placed in Data.Fin because Data.DepVec depends on Data.Fin.
--
-- The implementation was suggested by Conor McBride ("Fwd: how to
-- count 0..n-1", http://thread.gmane.org/gmane.comp.lang.agda/2554).

allFin : ∀ n → DepVec (Fin n) n
allFin _ = tabulate id

-}
