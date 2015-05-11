module CoreRegion.Ast.Typed where

open import Data.Nat
open import Data.Fin
open import Data.Vec

data Type : Set where
  unit : Type
  prim : Type
  pointer : Type → Type

data Expr (Prim : Set) : ∀ {n} → (tenv : Vec Type n) → Type → Set where

  prim-val : ∀ {n e}
             → Prim → Expr Prim {n} e prim

  prim-app : ∀ {n e a}
             → (Vec Prim a
             → Prim)
             → Vec Prim a
             → Expr Prim {n} e prim

  let-in   : ∀ {n e t u}
             → Expr Prim e t
             → Expr Prim (t ∷ e) u
             → Expr Prim {n} e u

  iden     : ∀ {n e}
             → (i : Fin n)
             → Expr Prim {n} e (lookup i e)

  ref      : ∀ {n e}
             → (i : Fin n)
             → Expr Prim {n} e (pointer (lookup i e))

  load     : ∀ {n e t}
             → Expr Prim {n} e (pointer t)
             → Expr Prim {n} e t

  store    : ∀ {n e t}
             → Expr Prim {n} e (pointer t)
             → Expr Prim {n} e t
             → Expr Prim {n} e unit

  seq      : ∀ {n e t}
             → Expr Prim {n} e unit
             → Expr Prim {n} e t
             → Expr Prim {n} e t

Closed : Set → Type → Set
Closed Prim Type = Expr Prim [] Type
