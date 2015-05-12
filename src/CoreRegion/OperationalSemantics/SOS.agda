module CoreRegion.OperationalSemantics.SOS (Prim : Set) where

open import Category.Functor
open RawFunctor {{...}}

open import Category.Applicative
--open RawApplicative {{...}}

open import Data.Empty
open import Data.Unit

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
open import Relation.Unary
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

open import CoreRegion.OperationalSemantics.SOS.Types Prim as CFG
open import CoreRegion.OperationalSemantics.SOS.Progress Prim as CFG

private instance vecFunctor : ∀ {l n} → RawFunctor {l} (flip Vec n)
vecFunctor = RawApplicative.rawFunctor Data.Vec.applicative

private instance maybeFunctor = Data.Maybe.functor

-- All terms are valid configurations
-- Where is deriving Functor/Foldable/Traversable when you need it...

{-# NON_TERMINATING #-}
-- BUT TOTALLY NOT ACTUALLY!
inject : ∀{n r e t} → ExprFix {n} {r} e t → Config {n} {r} e t
inject {n} {r} {e} {t} (fix exp)= help exp
  where recur = inject

        help : ∀{n r e t}
               → Expr ExprFix {n} {r} e t
               → Config {n} {r} e t
        help (prim-val p)      = expr $ prim-val p
        help (prim-app f args) = expr $ prim-app f $ recur <$> args
        help (let-in x y)      = expr $ let-in (recur x) (recur y)
        help (iden i {eq})     = expr (iden i {eq})
        help (ref i {eq})      = expr (ref i {eq})
        help (load x)          = expr $ load $ recur x
        help (store x y)       = expr $ store (recur x) (recur y)
        help (seq x y)         = expr $ seq (recur x) (recur y)


step : ∀ {n r e t}
       → (c  : Config {n} {r} e t)
       → {_ : isNonTerminal c}
       → Σ[ c' ∈ Config {n} {r} e t ] ((¬ (c' ≡ c)) × (isGood c'))
step (value _) = λ {}
step (expr exp) with exp

... | prim-val p = λ {_} → CFG.value (CFG.prim p) , (λ ()) , inj₁ tt

... | prim-app f args = {!!}

... | let-in x y = {!!}

... | iden i = {!!}

... | ref i = {!!}

... | load x = {!!}

... | store x y = {!!}

... | seq x y = {!!}
