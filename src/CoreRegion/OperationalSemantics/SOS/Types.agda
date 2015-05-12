module CoreRegion.OperationalSemantics.SOS.Types (Prim : Set) where

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

import Data.Fin as Fin
open Fin hiding (pred; suc)

open import Data.Vec
open import Data.Vec.All
open import Data.Product
open import Data.Sum
open import Data.Maybe hiding (All)

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

private instance vecFunctor : ∀ {l n} → RawFunctor {l} (flip Vec n)
vecFunctor = RawApplicative.rawFunctor Data.Vec.applicative

data Value : ∀{r} → Type r → Set where

  prim    : Prim → Value prim

  unit    : Value prim

  pointer : ∀ {r s le}
            → {t : Type r}
            → ℕ
            → Value $ pointer {r} s {le} t

data Config {n r} (e : Env n) (t : Type r) : Set where
  value : Value t → Config e t
  expr  : Expr Config e t → Config e t

ConfigSig : Set₁
ConfigSig = ∀ {n r e t} → Config {n} {r} e t → Set

isValue : ConfigSig
isValue (value _) = ⊤
isValue _         = ⊥

{-# NON_TERMINATING #-}
-- BUT TOTALLY NOT ACTUALLY!
dummy : ∀ {n r e t} → Config {n} {r} e t → ℕ
dummy (value _) = 1
dummy (expr exp) with exp
... | prim-val _ = 1
... | prim-app _ args = Data.Vec.foldr (const ℕ) ℕ._⊔_ 1 (dummy <$> args)
... | let-in x y = dummy x ⊔ dummy y
... | iden i = 1
... | ref i = 1
... | load x = dummy x
... | store x y = dummy x ⊔ dummy y
... | seq x y = dummy x ⊔ dummy y


{-# NON_TERMINATING #-}
-- BUT TOTALLY NOT ACTUALLY!
isExpr : ConfigSig
isExpr (value _) = ⊥
isExpr (expr exp) with exp
... | prim-val _ = ⊤
... | prim-app _ args = All isExpr args
... | let-in x y = isExpr x × isExpr y
... | iden i = ⊤
... | ref i = ⊤
... | load x = isExpr x
... | store x y = isExpr x × isExpr y
... | seq x y = isExpr x × isExpr y

Redex : ∀ {n r e t} → Expr Config {n} {r} e t → Set
Redex (prim-val _) = ⊤
Redex (prim-app _ args) = All isValue args
--Redex (let-in (value _) (value _)) = ⊤
Redex (let-in _         _)         = ⊥
Redex (iden i) = ⊤
Redex (ref i) = ⊤
Redex (load (value _)) = ⊤
Redex (load _)         = ⊥
Redex (store (value _) (value _)) = ⊤
Redex (store _         _)         = ⊥
Redex (seq (value _) (value _)) = ⊤
Redex (seq _         _)         = ⊥

mutual
  -- Sorry I stole your terminology, grammars
  NonTerminal : ∀ {n r e t} → Expr Config {n} {r} e t → Set
  NonTerminal e = Context e ⊎ Redex e

  Context : ∀ {n r e t} → Expr Config {n} {r} e t → Set
  Context (prim-val _) = ⊥
  Context {n} {e = e} {t = prim} (prim-app _ args) = p args
    where p : ∀{n} → Vec (Config e prim) n → Set
          p []               = ⊥
          p (value _   ∷ as) = p as
          p (expr  ctx ∷ as) = NonTerminal ctx × All isExpr as
  Context (let-in (expr ctx) e)          = NonTerminal ctx × isExpr e
  Context (let-in (value _)  (expr ctx)) = NonTerminal ctx
  Context (let-in _          _)          = ⊥
  Context (iden i) = ⊥
  Context (ref i) = ⊥
  Context (load (expr c))  = NonTerminal c
  Context (load (value _)) = ⊥
  Context (store (expr ctx) e)         = NonTerminal ctx × isExpr e
  Context (store (value _) (expr ctx)) = NonTerminal ctx
  Context (store _         _)          = ⊥
  Context (seq (expr ctx) e)         = NonTerminal ctx × isExpr e
  Context (seq (value _) (expr ctx)) = NonTerminal ctx
  Context (seq _         _)          = ⊥

isNonTerminal : ConfigSig
isNonTerminal (value _) = ⊥
isNonTerminal (expr  e) = NonTerminal e

isRedex : ConfigSig
isRedex (value _) = ⊥
isRedex (expr  e) = Redex e

isContext : ConfigSig
isContext (value _) = ⊥
isContext (expr  e) = Context e

isGood : ConfigSig
isGood e = (isValue e ⊎ isRedex e ⊎ isContext e)
