module CoreRegion.Ast.Regioned where

open import Category.Functor
open RawFunctor {{...}}

open import Category.Applicative
--open RawApplicative {{...}}

open import Data.Empty
open import Data.Unit

import Data.Nat
open Data.Nat hiding (pred; suc)

import Data.Fin
open Data.Fin hiding (pred; suc)

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

module T where

  data Type : Set where
    unit : Type
    prim : Type
    pointer : Region → Type → Type

  nonZero : Type → Set
  nonZero (pointer r t) = R.nonZero r × nonZero t
  nonZero _             = ⊤

  suc : Type → Type
  suc (pointer r t) = pointer (R.suc r) $ suc t
  suc basicT        = basicT

  pred : (t : Type) → {_ : nonZero t} → Type
  pred (pointer r t) {rnz , tnz} = pointer (R.pred' r {rnz}) $ pred t {tnz}
  pred basicT                    = basicT

open T hiding (suc; pred) public

Env : ℕ → Set
Env n = Vec Type n



private instance vecFunctor : ∀ {l n} → RawFunctor {l} (flip Vec n)
vecFunctor = RawApplicative.rawFunctor Data.Vec.applicative

data Expr (Prim : Set) : ∀ {n} → (tenv : Env n) → Type → Set where

  prim-val : ∀ {n e}
             → Prim
             → Expr Prim {n} e prim

  prim-app : ∀ {n e a}
             → (Vec Prim a
             → Prim)
             → Vec Prim a
             → Expr Prim {n} e prim

  let-in   : ∀ {n e t u}
             → {good : nonZero u}
             → Expr Prim e t
             → Expr Prim (t ∷ (T.suc <$> e)) u
             → Expr Prim {n} e (T.pred u {good})

  iden     : ∀ {n e}
             → (i : Fin n)
             → Expr Prim {n} e (lookup i e)

  ref      : ∀ {n e}
             → (i : Fin n)
             → Expr Prim {n} e (pointer (just (toℕ i)) (lookup i e))

  load     : ∀ {n e t r}
             → Expr Prim {n} e (pointer r t)
             → Expr Prim {n} e t

  store    : ∀ {n e t r}
             → Expr Prim {n} e (pointer r t)
             → Expr Prim {n} e t
             → Expr Prim {n} e unit

  seq      : ∀ {n e} {t : Type}
             → Expr Prim {n} e unit
             → Expr Prim {n} e t
             → Expr Prim {n} e t

Closed : Set → Type → Set
Closed Prim Type = Expr Prim [] Type
