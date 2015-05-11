module CoreRegion.OperationalSemantics.Types (Prim : Set) where

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


data Value : ∀{r} → Type r → Set where

  prim    : Prim → Value prim

  unit    : Value prim

  pointer : ∀ {r s le}
            → {t : Type r}
            → ℕ
            → Value $ pointer {r} s {le} t

-- Every Σ-type is a risk....
Stack : Set
Stack = List (Σ[ r ∈ Region ] Σ[ t ∈ Type r ] Value t)

{-
private ConfigFun : ∀ {r n}
                    → {typ : Type r}
                    → {env : Env n}
                    → (exp : Expr env typ)
                    → (stk : Stack)
                    → Set
ConfigFun (prim-val x) = {!!}
ConfigFun (prim-app x x₁) = {!!}
ConfigFun (let-in exp exp₁) = {!!}
ConfigFun (iden i) = {!!}
ConfigFun (ref i) = {!!}
ConfigFun (load x) = {!!}
ConfigFun (store x exp) = {!!}
ConfigFun (seq exp exp₁) = {!!}
-}
