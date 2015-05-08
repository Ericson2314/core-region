module CoreRegion.Ast.Regioned where

open import Category.Functor

open import Data.Empty

open import Data.Nat hiding (_≤_)
open import Data.Fin hiding (_≤_)
open import Data.Vec
open import Data.List
open import Data.Product
open import Data.Maybe

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Function

import CoreRegion.Region as R
open R using (Region)


data Type : (r : Region) → Set where
  unit : Type nothing
  prim : Type nothing
  --pointer : ∀ r2 → (Σ[ r1 ∈ Region ] (Type r1)) → Type r2 -- might need to tighten
  pointer : ∀ r2 → Type nothing → Type r2 -- might need to tighten

decrementE : {r : Region} {w : ¬ (r ≡ just 0)} → Type r → Type (R.pred r {w})
decrementE = λ
  { unit → unit
  ; prim → prim
  ; {r} {w} (pointer .r x) → pointer (R.pred r {w}) x -- (R.pred _) x
  }

Env : ℕ → Set
--Env n = Vec (Σ[ r ∈ Region ] (Type r)) n
Env n = Vec (Type nothing) n


data Ast (Prim : Set) : ∀ {n r} → (tenv : Env n) → Type r → Set where
  prim-val : ∀ {n e} → Prim → Ast Prim {n} e prim
  prim-app : ∀ {n e a} → (Vec Prim a → Prim) → Vec Prim a → Ast Prim {n} e prim

  let-in   : ∀ {n e r t}
             → (good : ¬ (r ≡ just 0))
             → (u : Type r)
             → Ast Prim e t
--             → Ast Prim ((r , t) ∷ e) u
             → Ast Prim (t ∷ e) u
             → Ast Prim {n} e (decrementE {r} {good} u)

  --iden     : ∀ {n e} → (i : Fin n) → Data.Product.map id (λ x → Ast Prim {n} e x) (lookup i e)
  iden     : ∀ {n e} → (i : Fin n) → Ast Prim {n} e (lookup i e)

  ref      : ∀ {n e} → (i : Fin n) → Ast Prim {n} e (pointer (just (toℕ i)) (lookup i e))
  load     : ∀ {n e t r} → Ast Prim {n} e (pointer r t) → Ast Prim {n} e t
  store    : ∀ {n e t r} → Ast Prim {n} e (pointer r t) → Ast Prim {n} e t → Ast Prim {n} e unit

  seq      : ∀ {n e r} {t : Type r} → Ast Prim {n} e unit → Ast Prim {n} e t → Ast Prim {n} e t

Closed : (r : Region) → Set → Type r → Set
Closed _ Prim Type = Ast Prim [] Type
