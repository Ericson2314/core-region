module CoreRegion.Ast.Untyped where

open import Data.Nat
open import Data.Fin
open import Data.Vec

data Ast (Prim : Set) : (maxI : ℕ) → Set where
  prim-val : ∀ n → Prim → Ast Prim n
  prim-app : ∀ n v → (Vec Prim v → Prim) → Vec Prim v → Ast Prim n

  let-in   : ∀ n → Ast Prim n → Ast Prim (suc n) → Ast Prim n
  iden     : ∀ n → Fin n → Ast Prim n

  ref      : ∀ n → Fin n → Ast Prim n
  load     : ∀ n → Ast Prim n → Ast Prim n
  store    : ∀ n → Ast Prim n → Ast Prim n → Ast Prim n

  seq      : ∀ n → Ast Prim n → Ast Prim n → Ast Prim n

Closed : Set → Set
Closed Prim = Ast Prim 0
