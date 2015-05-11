module CoreRegion.Region where

open import Category.Functor

open import Data.Empty

import Data.Nat as ℕ
open ℕ using (ℕ; zero)
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple

import Data.Fin
open Data.Fin using (Fin)

open import Data.Vec
open import Data.List
open import Data.Product
open import Data.Sum
open import Data.Maybe

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Function


Region : Set
Region = Maybe ℕ


nonZero : Region → Set
nonZero r = ¬ (r ≡ just 0)

suc : Region → Region
suc = λ
  { nothing → nothing
  ; (just n) → just (ℕ.suc n)
  }

pred : Region → Region
pred nothing = nothing
pred (just n) = just (ℕ.pred n)

pred' : (r : Region) → { _ : nonZero r } → Region
pred' nothing = nothing
pred' (just n) {w} with n
... | 0 = ⊥-elim $ w refl
... | ℕ.suc m = just m


data _≤_ : Region → Region → Set where
  ≤Ω : ∀ {r} → r ≤ nothing
  z≤n : ∀ {n} → just zero ≤ just n
  s≤s : ∀ {m n} → (just m ≤ just n) → just (ℕ.suc m) ≤ just (ℕ.suc n)

≤-suc : ∀ {a b} → a ≤ b → suc a ≤ suc b
≤-suc {_}       {nothing} ≤Ω = ≤Ω
≤-suc {nothing} {just _}  ()
≤-suc {just a}  {just b}  p  = s≤s p

≤-pred : ∀ {a b} {x : nonZero a} {y : nonZero b}
         → a ≤ b → pred' a {x} ≤ pred' b {y}
≤-pred {_}       {nothing} _ = ≤Ω
≤-pred {nothing} {just _} ()
≤-pred {just (ℕ.suc a)} {just (ℕ.suc b)} (s≤s x) = x
≤-pred {a = just 0} {x = nz} _ = ⊥-elim $ nz refl
≤-pred {b = just 0} {y = nz} _ = ⊥-elim $ nz refl

_≟_ : Decidable {A = Region} _≡_
nothing ≟ just _ = no λ()
just _ ≟ nothing = no λ()
just zero ≟ just (ℕ.suc _) = no λ()
just (ℕ.suc _) ≟ just zero = no λ()
just zero  ≟ just zero   = yes refl
nothing  ≟ nothing = yes refl
just (ℕ.suc m) ≟ just (ℕ.suc n)  with just m ≟ just n
just (ℕ.suc m) ≟ just (ℕ.suc .m) | yes refl = yes refl
just (ℕ.suc m) ≟ just (ℕ.suc n)  | no prf   = no (prf ∘ PropEq.cong pred)

_≤?_ : Decidable _≤_
_              ≤? nothing    = yes ≤Ω
just zero      ≤? just n     = yes z≤n
just (ℕ.suc m) ≤? just zero  = no λ()
nothing        ≤? just n     = no λ()
just (ℕ.suc m) ≤? just (ℕ.suc n) with just m ≤? just n
... | yes m≤n = yes (_≤_.s≤s m≤n)
... | no  m≰n = no  (λ { (s≤s pred') → m≰n pred' })

decTotalOrder : DecTotalOrder _ _ _
decTotalOrder = record
  { Carrier         = Region
  ; _≈_             = _≡_
  ; _≤_             = _≤_
  ; isDecTotalOrder = record
      { isTotalOrder = record
          { isPartialOrder = record
              { isPreorder = record
                  { isEquivalence = PropEq.isEquivalence
                  ; reflexive     = refl'
                  ; trans         = trans
                  }
              ; antisym  = antisym
              }
          ; total = total
          }
      ; _≟_  = _≟_
      ; _≤?_ = _≤?_
      }
  }
  where
  refl' : _≡_ ⇒ _≤_
  refl' {nothing} refl = ≤Ω
  refl' {just zero} refl = z≤n
  refl' {just (ℕ.suc x)} refl = s≤s (refl' {just x} refl)

  antisym : Antisymmetric _≡_ _≤_
  antisym ≤Ω        ≤Ω  = refl
  antisym z≤n       z≤n = refl
  antisym (s≤s m≤n) (s≤s n≤m) with antisym m≤n n≤m
  ...                         | refl = refl

  trans : Transitive _≤_
  trans ≤Ω ≤Ω = ≤Ω
  trans z≤n ≤Ω = ≤Ω
  trans z≤n z≤n = z≤n
  trans z≤n (s≤s x) = z≤n
  trans (s≤s x) ≤Ω = ≤Ω
  trans (s≤s x) (s≤s y) = s≤s $ trans x y

  total : Total _≤_
  total (just _) nothing  = inj₁ ≤Ω
  total nothing (just _)  = inj₂ ≤Ω
  total nothing nothing   = inj₁ ≤Ω
  total (just zero) (just zero) = inj₁ z≤n
  total (just zero) (just (ℕ.suc y)) = inj₁ z≤n
  total (just (ℕ.suc x)) (just zero) = inj₂ z≤n
  total (just (ℕ.suc x)) (just (ℕ.suc y)) with total (just x) (just y)
  ... | inj₁ m≤n = inj₁ (s≤s m≤n)
  ... | inj₂ n≤m = inj₂ (s≤s n≤m)

ℕ≤-to-≤ : ℕ._≤_ ⇒ λ x y → just x ≤ just y
ℕ≤-to-≤ {zero} {zero} ℕ.z≤n = z≤n
ℕ≤-to-≤ {zero} {ℕ.suc j} ℕ.z≤n = z≤n
ℕ≤-to-≤ {ℕ.suc i} {zero} ()
ℕ≤-to-≤ {ℕ.suc i} {ℕ.suc j} (ℕ.s≤s z) = s≤s (ℕ≤-to-≤ z)

nonZero-trans : ∀ {r1 r2}
              → nonZero r1
              → r1 ≤ r2
              → nonZero r2
nonZero-trans _ ≤Ω = λ()
nonZero-trans _ (s≤s _) = λ ()
nonZero-trans nz z≤n = λ _ → nz refl

_+_ : Region → Region → Region
just n + just m = just (n ℕ.+ m)
_      + _      = nothing

+-≤ : ∀ {r1 r2} → r1 ≤ (r1 + r2)
+-≤ {nothing} = ≤Ω
+-≤ {just _} {nothing} = ≤Ω
+-≤ {just a} {just b} = ℕ≤-to-≤ z
  where open DecTotalOrder ℕ.decTotalOrder
        x : a ℕ.≤ b ℕ.+ a
        x = ≤-steps {a} {a} b $ reflexive PropEq.refl

        y : b ℕ.+ a ℕ.≤ a ℕ.+ b
        y = reflexive $ +-comm b a

        z = trans x y
