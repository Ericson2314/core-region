module CoreRegion.Ast.Typed where

open import Data.Nat
open import Data.Fin
open import Data.Vec

data Type : Set where
  unit : Type
  prim : Type
  pointer : Type → Type

Env : ℕ → Set
Env n = Vec Type n

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
               → Expr Recur e t
               → Expr Recur (t ∷ e) u
               → Expr Recur {n} e u

    iden     : ∀ {n e}
               → (i : Fin n)
               → Expr Recur {n} e (lookup i e)

    ref      : ∀ {n e}
               → (i : Fin n)
               → Expr Recur {n} e (pointer (lookup i e))

    load     : ∀ {n e t}
               → Expr Recur {n} e (pointer t)
               → Expr Recur {n} e t

    store    : ∀ {n e t}
               → Expr Recur {n} e (pointer t)
               → Expr Recur {n} e t
               → Expr Recur {n} e unit

    seq      : ∀ {n e t}
               → Expr Recur {n} e unit
               → Expr Recur {n} e t
               → Expr Recur {n} e t

  data ExprFix : ExprSig where
    fix : ∀{n}
          → (e : Env n)
          → (t : Type)
          → Expr ExprFix e t
          → ExprFix e t

  Closed : Type → Set
  Closed Type = Expr ExprFix [] Type
