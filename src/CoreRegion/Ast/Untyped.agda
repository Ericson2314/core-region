module CoreRegion.Ast.Untyped where

open import Data.Nat
open import Data.Fin
open import Data.Vec


module E (Prim : Set) where

  ExprSig : Set₁
  ExprSig = (maxI : ℕ) → Set

  data Expr (Recur : ExprSig) : ExprSig where

    prim-val : ∀ n
               → Prim
               → Expr Recur n

    prim-app : ∀ n v
               → (Vec Prim v → Prim)
               → Vec Prim v
               → Expr Recur n

    let-in   : ∀ n
               → Recur n
               → Recur (suc n)
               → Expr Recur n

    iden     : ∀ n
               → Fin n
               → Expr Recur n

    ref      : ∀ n
               → Fin n
               → Expr Recur n

    load     : ∀ n
               → Recur n
               → Expr Recur n
    store    : ∀ n
               → Recur n
               → Recur n
               → Expr Recur n

    seq      : ∀ n
               → Recur n
               → Recur n
               → Expr Recur n

  data ExprFix : ExprSig where
    fix : ∀ n
          → Expr ExprFix n
          → ExprFix n

  Closed : Set
  Closed = Expr ExprFix 0
