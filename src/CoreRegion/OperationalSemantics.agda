module CoreRegion.OperationalSemantics (Prim : Set) where

open import Category.Functor
open RawFunctor {{...}}

open import Category.Applicative
--open RawApplicative {{...}}

open import Category.Functor
open import Category.Monad
open import Category.Monad.State

open import Data.Empty

import Data.Nat as ℕ
open ℕ hiding (pred; suc; _≤_)
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
open PropEq.≡-Reasoning

open import Function

import CoreRegion.Region as R
open R using (Region)

import CoreRegion.Ast.RegionIndexed as AST_RI
open AST_RI
open AST_RI.E Prim

open import CoreRegion.OperationalSemantics.Types Prim

private instance vecFunctor : ∀ {l n} → RawFunctor {l} (flip Vec n)
vecFunctor = RawApplicative.rawFunctor Data.Vec.applicative

private instance maybeFunctor = Data.Maybe.functor

inject : ∀{t} → Closed t → Configuration 0 [] t

inject (fix (let-in
             {s = just 0}
             {u = pointer (just 0) t}
             {nz = nz}
             _
             _))
       {t = T.pred {just 0} {.nz} (pointer (just 0) t)}
       = ?
  where x : Set
        x = T.pred {just 0} {nz} (pointer (just 0) t)
{-
inject (let-in
        {0}
        {[]}
        {nothing}
        {s = just 0}
        {t}
        {u}
{s = just (ℕ.suc s)} _ _) = {!!}
-}
inject x = {!!}

{-
step : ∀ {r}
       → {t : Type r}
       → (stk : Stack stack-len)
       → {env : Env env-len}
       → {typ : Type r}
       → {typ : Type r}
step = {!!}
-}
