module CoreRegion.Ast.Typed where

open import Data.Nat
open import Data.Fin
open import Data.Vec

data Type : Set where
  unit : Type
  prim : Type
  pointer : Type → Type

data Ast (Prim : Set) : ∀ {n} → (tenv : Vec Type n) → Type → Set where
  prim-val : ∀ {n e} → Prim → Ast Prim {n} e prim
  prim-app : ∀ {n e a} → (Vec Prim a → Prim) → Vec Prim a → Ast Prim {n} e prim

  let-in   : ∀ {n e t u} → Ast Prim e t → Ast Prim (t ∷ e) u → Ast Prim {n} e u
  iden     : ∀ {n e} → (i : Fin n) → Ast Prim {n} e (lookup i e)

  ref      : ∀ {n e} → (i : Fin n) → Ast Prim {n} e (pointer (lookup i e))
  load     : ∀ {n e t} → Ast Prim {n} e (pointer t) → Ast Prim {n} e t
  store    : ∀ {n e t} → Ast Prim {n} e (pointer t) → Ast Prim {n} e t → Ast Prim {n} e unit

  seq      : ∀ {n e t} → Ast Prim {n} e unit → Ast Prim {n} e t → Ast Prim {n} e t

Closed : Set → Type → Set
Closed Prim Type = Ast Prim [] Type
