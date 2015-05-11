module CoreRegion.Progs where

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
open AST_RI.E ℕ

m+ : Vec ℕ 2 → ℕ
m+ (x ∷ y ∷ []) = x ℕ.+ y

m- : Vec ℕ 2 → ℕ
m- (x ∷ y ∷ []) = x ℕ.∸ y

m* : Vec ℕ 2 → ℕ
m* (x ∷ y ∷ []) = x ℕ.∸ y

n0 : Closed prim
n0 = fix $ prim-val zero

n2 : Closed prim
n2 = fix $ prim-app m* (n0 ∷ n0 ∷ [])

-- let 2 to stack and then iden it
remember2 : Closed prim
remember2 = fix $ let-in
                  -- {n = 0}
                  -- {e = []}
                  -- {r = nothing}
                  -- {s = nothing}
                  -- {t = prim}
                  -- {u = prim}
                  {nz = λ ()}
                  n2
                  $ fix $ iden
                          -- {t = prim}
                          (fromℕ 0)
                          {eq = refl}

-- let 2 to stack, mutate it to 1, and move it off
mutate3 : Closed prim
mutate3 = fix $ let-in
                {nz = λ()}
                n2
                $ fix $ let-in
                        {nz = λ ()}
                        ( fix $ ref
                                Fin.zero
                                {eq = refl})
                        $ fix $ seq
                                ( fix $ store
                                        -- {t = prim}
                                        ( fix $ iden
                                                --{ t = pointer
                                                --      {nothing}
                                                --      (just 0)
                                                --      {R.≤Ω}
                                                --      prim}
                                                Fin.zero
                                                {eq = refl})
                                        $ fix $ prim-val zero)
                                $ fix $ iden
                                        (Fin.suc Fin.zero)
                                        {eq = refl}
