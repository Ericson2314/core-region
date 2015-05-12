------------------------------------------------------------------------
-- Adopted from the Agda standard library
--
-- Lists where all elements satisfy a given property
------------------------------------------------------------------------

module Data.Vec.All where

open import Data.Vec as Vec hiding (map; head; tail; lookup; tabulate)
import Data.Nat as ℕ
open import Function
open import Level
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Unary using (Decidable) renaming (_⊆_ to _⋐_)
open import Relation.Binary.PropositionalEquality

-- All P xs means that all elements in xs satisfy P.

infixr 5 _∷_

data All {a p} {A : Set a}
         (P : A → Set p) : ∀ {n} → Vec A n → Set (p ⊔ a) where
  []  : All P {0} []
  _∷_ : ∀ {x n xs} (px : P x) (pxs : All P {n} xs) → All P (x ∷ xs)

head : ∀ {a p} {A : Set a} {P : A → Set p} {n xs} →
       All P {ℕ.suc n} xs → P $ Vec.head xs
head (px ∷ pxs) = px

tail : ∀ {a p} {A : Set a} {P : A → Set p} {n xs} →
       All P {ℕ.suc n} xs → All P $ Vec.tail xs
tail (px ∷ pxs) = pxs

lookup : ∀ {a p} {A : Set a} {P : A → Set p} {n xs} →
         All P {n} xs → (∀ {x : A} → x ∈ xs → P x)
lookup []         ()
lookup (px ∷ pxs) here = px
lookup (px ∷ pxs) (there x∈xs) = lookup pxs x∈xs

tabulate : ∀ {a p} {A : Set a} {P : A → Set p} {n xs} →
           (∀ {x} → x ∈ xs → P x) → All P {n} xs
tabulate {xs = []}     hyp = []
tabulate {xs = x ∷ xs} hyp = hyp here ∷ tabulate (hyp ∘ there)

map : ∀ {a p q n} {A : Set a} {P : A → Set p} {Q : A → Set q} →
      P ⋐ Q → All P {n} ⋐ All Q {n}
map g []         = []
map g (px ∷ pxs) = g px ∷ map g pxs

all : ∀ {a p n} {A : Set a} {P : A → Set p} →
      Decidable P → Decidable (All P {n})
all p []       = yes []
all p (x ∷ xs) with p x
all p (x ∷ xs) | yes px = Dec.map′ (_∷_ px) tail (all p xs)
all p (x ∷ xs) | no ¬px = no (¬px ∘ head)
