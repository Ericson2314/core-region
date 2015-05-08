module CoreRegion.Region where

open import Category.Functor

open import Data.Empty

import Data.Nat
open Data.Nat using (ℕ; zero)

import Data.Fin
open Data.Fin using (Fin)

open import Data.Vec
open import Data.List
open import Data.Product
open import Data.Maybe

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Function


Region : Set
Region = Maybe ℕ

data _≤_ : Region → Region → Set where
  ≤Ω : ∀ {r} → r ≤ nothing
  z≤n : ∀ {n} → just zero ≤ just n
  s≤s : ∀ {m n} → (just m ≤ just n) → just (ℕ.suc m) ≤ just (ℕ.suc n)

nonZero : Region → Set
nonZero r = ¬ (r ≡ just 0)

suc : Region → Region
suc = λ
  { nothing → nothing
  ; (just n) → just (ℕ.suc n)
  }

≤-suc : ∀ {a b} → a ≤ b → suc a ≤ suc b
≤-suc {_}       {nothing} ≤Ω = ≤Ω
≤-suc {nothing} {just _}  ()
≤-suc {just a}  {just b}  p  = s≤s p

pred : (r : Region) → { _ : nonZero r } → Region
pred nothing = nothing
pred (just n) {w} with n
... | 0     = ⊥-elim $ w refl
... | Data.Nat.suc m = just m

≤-pred : ∀ {a b} {x : nonZero a} {y : nonZero b}
         → a ≤ b → pred a {x} ≤ pred b {y}
≤-pred {_}       {nothing} _ = ≤Ω
≤-pred {nothing} {just _} ()
≤-pred {just (Data.Nat.suc a)} {just (Data.Nat.suc b)} (s≤s x) = x
≤-pred {a = just 0} {x = nz} _ = ⊥-elim $ nz refl
≤-pred {b = just 0} {y = nz} _ = ⊥-elim $ nz refl

_≤?_ : Decidable _≤_
_            ≤? nothing    = yes ≤Ω
just zero    ≤? just n     = yes z≤n
just (Data.Nat.suc m) ≤? just zero  = no λ()
nothing      ≤? just n     = no λ()
just (Data.Nat.suc m) ≤? just (Data.Nat.suc n) with just m ≤? just n
... | yes m≤n = yes (_≤_.s≤s m≤n)
... | no  m≰n = no  (λ { (s≤s pred) → m≰n pred })
