module CoreRegion.Ast.Untyped where

open import Data.Nat
open import Data.Fin
open import Data.Vec

data Expr (Prim : Set) : (maxI : ℕ) → Set where

  prim-val : ∀ n
             → Prim
             → Expr Prim n

  prim-app : ∀ n v
             → (Vec Prim v → Prim)
             → Vec Prim v
             → Expr Prim n

  let-in   : ∀ n
             → Expr Prim n
             → Expr Prim (suc n)
             → Expr Prim n

  iden     : ∀ n
             → Fin n
             → Expr Prim n

  ref      : ∀ n
             → Fin n
             → Expr Prim n

  load     : ∀ n
             → Expr Prim n
             → Expr Prim n
  store    : ∀ n
             → Expr Prim n
             → Expr Prim n
             → Expr Prim n

  seq      : ∀ n
             → Expr Prim n
             → Expr Prim n
             → Expr Prim n

Closed : Set → Set
Closed Prim = Expr Prim 0
