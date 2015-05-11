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

module E (Prim : Set) where

  ExprSig : Set₁
  ExprSig = ∀ {n} → (tenv : Env n) → Type → Set

  data Expr (Recur : ExprSig) : ExprSig where

    prim-val : ∀ {n e}
               → Prim
               → Expr Recur {n} e prim

    prim-app : ∀ {n e a}
               → (Vec Prim a → Prim)
               → Vec (Recur {n} e prim) a
               → Expr Recur {n} e prim

    let-in   : ∀ {n e t u}
               → {nz : nonZero u}
               → Recur e t
               → Recur (t ∷ (T.suc <$> e)) u
               → Expr Recur {n} e (T.pred u {nz})

    iden     : ∀ {n e}
               → (i : Fin n)
               → Expr Recur {n} e (lookup i e)

    ref      : ∀ {n e}
               → (i : Fin n)
               → Expr Recur {n} e (pointer (just (toℕ i)) (lookup i e))

    load     : ∀ {n e t r}
               → Recur {n} e (pointer r t)
               → Expr Recur {n} e t

    store    : ∀ {n e t r}
               → Recur {n} e (pointer r t)
               → Recur {n} e t
               → Expr Recur {n} e unit

    seq      : ∀ {n e} {t : Type}
               → Recur {n} e unit
               → Recur {n} e t
               → Expr Recur {n} e t

  data ExprFix : ExprSig where
    fix : ∀{n}
          → (e : Env n)
          → (t : Type)
          → Expr ExprFix e t
          → ExprFix e t

  Closed : Type → Set
  Closed Type = Expr ExprFix [] Type
