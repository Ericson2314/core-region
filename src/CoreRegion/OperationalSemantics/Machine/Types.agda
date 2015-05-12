module CoreRegion.OperationalSemantics.Machine.Types (Prim : Set) where

open import Category.Functor
open RawFunctor {{...}}

open import Category.Applicative
--open RawApplicative {{...}}

open import Data.Empty
open import Data.Unit
open import Data.Bool

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


data Value : ∀{r} → Type r → Set where

  prim    : Prim → Value prim

  unit    : Value prim

  pointer : ∀ {r s le}
            → {t : Type r}
            → ℕ
            → Value $ pointer {r} s {le} t

data Node {n r} (e : Env n) (t : Type r) : Set where
  hole  : Node e t
  value : Value t → Node e t
  expr  : ExprFix e t → Node e t

SSExpr = Expr Node

isValue : ∀ {n r e t} → Node {n} {r} e t → Set
isValue (value _) = ⊤
isValue _         = ⊥

isExpr : ∀ {n r e t} → Node {n} {r} e t → Set
isExpr (expr _) = ⊤
isExpr _        = ⊥

isHole : ∀ {n r e t} → Node {n} {r} e t → Set
isHole hole = ⊤
isHole _    = ⊥

Redex : ∀ {n r e t} → SSExpr {n} {r} e t → Set
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

Context : ∀ {n r e t} → SSExpr {n} {r} e t → Set
Context (prim-val _) = ⊥
Context {n} {e = e} {t = prim} (prim-app _ args) = p args
  where p : ∀{n} → Vec (Node e prim) n → Set
        p []             = ⊥
        p (value _ ∷ as) = p as
        p (hole    ∷ as) = All isExpr as
        p (expr _  ∷ _)  = ⊥
Context (let-in hole      (expr _)) = ⊤
Context (let-in (value _) hole)     = ⊤
Context (let-in _         _)        = ⊥
Context (iden i) = ⊥
Context (ref i) = ⊥
Context (load hole) = ⊤
Context (load _)    = ⊥
Context (store hole      (expr _)) = ⊤
Context (store (value _) hole)     = ⊤
Context (store _         _)        = ⊥
Context (seq hole      (expr _)) = ⊤
Context (seq (value _) hole)     = ⊤
Context (seq _         _)        = ⊥

ΣContext : ExprSig
ΣContext {n} {r} e t = Σ[ sse ∈ SSExpr {n} {r} e t ] Context sse

{-
WithHoleMatching : ∀ {n r e t} {n' r'}
                   → (e' : Env n')
                   → (t' : Type r')
                   → (c , _  : ΣContext)
                   → {_ : Context c}
                   → (c  : SSExpr {n} {r} e t)
WithHoleMatching _ _ (E.prim-val _) = λ {}
WithHoleMatching e' t' (E.prim-app _ []) = {!!}
WithHoleMatching e' t' (E.prim-app _ (x₁ ∷ y)) = {!!}
WithHoleMatching e' t' (E.let-in x y) = {!!}
WithHoleMatching _ _ (E.iden _) = λ {}
WithHoleMatching _ _ (E.ref _) = λ {}
WithHoleMatching e' t' (E.load (hole {e = .e'} {t = .t'})) = ⊤
WithHoleMatching e' t' (E.load (value x)) = λ {}
WithHoleMatching e' t' (E.load (expr x)) = λ {}
WithHoleMatching e' t' (E.store hole hole) = λ {}
WithHoleMatching e' t' (E.store hole (value x)) = λ {}
WithHoleMatching e' t' (E.store hole (expr x)) = {!!}
WithHoleMatching e' t' (E.store (value x) hole) = {!!}
WithHoleMatching e' t' (E.store (value x) (value x₁)) = {!!}
WithHoleMatching e' t' (E.store (value x) (expr x₁)) = {!!}
WithHoleMatching e' t' (E.store (expr x) _) = λ {}
WithHoleMatching e' t' (E.seq hole hole) = {!!}
WithHoleMatching e' t' (E.seq hole (value x)) = {!!}
WithHoleMatching e' t' (E.seq hole (expr x)) = {!!}
WithHoleMatching e' t' (E.seq (value x) hole) = {!!}
WithHoleMatching e' t' (E.seq (value x) (value x₁)) = {!!}
WithHoleMatching e' t' (E.seq (value x) (expr x₁)) = {!!}
WithHoleMatching e' t' (E.seq (expr x) y) = λ {}
-}
{-
data Configuration : ExprSig where
  unvisited :
-}


-- How many let bindings back can we index?
let-succ : ∀ {n r e t}
           → ΣContext {n} {r} e t
           → (ℕ → ℕ)
let-succ (let-in _ _ , _) = ℕ.suc
let-succ _            = id


-- Pointers gotta be valid!
-- TODO: Why is this discontinuous?
region-stacklen : Region → ℕ → Set
region-stacklen nothing  n = ⊤
region-stacklen (just r) n = r ℕ.≤ n

env-stacklen : ℕ → ℕ → Set
env-stacklen = ℕ._≤_

-- `m` represents the number of lets in the stack
data CallStack : (m : ℕ)
                 → {n : ℕ}
                 → {r : Region}
                 → (e : Env n)
                 → (t : Type r)
                 → Set
                 where

  halt  : {t : Type nothing}
          → CallStack 0 [] t

  frame : ∀ {n r e t}
             {m n' r' e' t'}
          → (cxt : ΣContext {n} {r} e t)
          → {_ : region-stacklen r m}
          → {_ : env-stacklen n m}
          → CallStack m {n'} {r'} e' t'
          → CallStack (let-succ cxt m) {n} {r} e t

record Configuration (m : ℕ)
                     {n : ℕ}
                     {r : Region}
                     (e : Env n)
                     (t : Type r)
                     : Set
                     where
  field
    unvisited           : ExprFix {n} {r} e t
    callStack           : CallStack m {n} {r} e t
    prf-region-stacklen : region-stacklen r m
    prf-env-stacklen    : env-stacklen n m


-- Every Σ-type is a risk....
--Stack : Set
--Stack = List (Σ[ r ∈ Region ] Σ[ t ∈ Type r ] Value t)

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
