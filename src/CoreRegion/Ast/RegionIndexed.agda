module CoreRegion.Ast.RegionIndexed where

open import Category.Functor
open RawFunctor {{...}}

open import Category.Applicative
--open RawApplicative {{...}}

open import Data.Empty
open import Data.Unit

import Data.Nat as ℕ
open ℕ hiding (pred; suc)
open import Data.Nat.Properties.Simple

import Data.Fin as Fin
open Fin hiding (pred; suc)

open import Data.Vec
open import Data.List
open import Data.Product
open import Data.Maybe

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Function

import CoreRegion.Region as R
open R using (Region)

module T where

  data Type : (r : Region) → Set where
    unit : Type nothing
    prim : Type nothing
    -- order constraint ensures the lifetime of pointer is less than lifetime of
    pointer : ∀ {r1} → ∀ r2 → { _ : r2 R.≤ r1 } → (Type r1) → Type r2

  nonZero : ∀ {r} → Type r → Set
  nonZero (pointer r t) = R.nonZero r × nonZero t
  nonZero _             = ⊤

  regionSaysEnough : ∀ {r} → {nz : R.nonZero r} → (t : Type r) → nonZero t
  regionSaysEnough unit = record {}
  regionSaysEnough prim = record {}
  regionSaysEnough {r} {nz} (pointer {r'} .r {le} t) =
    (nz , regionSaysEnough {r'} {R.nonZero-trans nz le} t)

  suc : ∀{r} → Type r → Type (R.suc r)
  suc     unit                     = unit
  suc     prim                     = prim
  suc {r} (pointer {r'} .r {le} t) = pointer (R.suc r) {R.≤-suc le} (suc t)

  pred : {r : Region} {w : R.nonZero r} → Type r → Type (R.pred' r {w})
  pred unit = unit
  pred prim = prim
  pred {r} {nz} (pointer {r'} .r {le} t) = pointer
                                           {R.pred' r' {R.nonZero-trans nz le}}
                                           (R.pred' r {nz})
                                           {R.≤-pred le}
                                           (pred t)

open T hiding (suc; pred) public


Env : ℕ → Set
Env n = Vec (Σ[ r ∈ Region ] (Type r)) n

private instance vecFunctor : ∀ {l n} → RawFunctor {l} (flip Vec n)
vecFunctor = RawApplicative.rawFunctor Data.Vec.applicative

t-subst : ∀{l} → {A B : Set l} → (_ : A ≡ B) → A → B
t-subst {_} {A} {.A} refl x = x

beef-up : {A : ℕ → Set }
          → (∀{m} → A m → A (ℕ.suc m))
          → (n : ℕ)
          → (∀{m} → A m → A (n ℕ.+ m))
beef-up _ zero = id
beef-up {A} f (ℕ.suc n) {m} = rst ∘ f {m}
  where rst : A (ℕ.suc m) → A ((ℕ.suc n) ℕ.+ m)
        rst x = t-subst (cong A (eq {n} {m})) ret
          where ret : A (n ℕ.+ (ℕ.suc m))
                ret = beef-up {A} f n {ℕ.suc m} x

                eq : ∀{n m} → (n ℕ.+ (ℕ.suc m)) ≡ ((ℕ.suc n) ℕ.+ m)
                eq {zero} = refl
                eq {ℕ.suc n} {m} =
                  begin
                    ℕ.suc n ℕ.+ ℕ.suc m
                  ≡⟨ +-suc (ℕ.suc n) m ⟩
                    ℕ.suc (ℕ.suc n ℕ.+ m)
                  ≡⟨ refl ⟩
                    ℕ.suc (ℕ.suc n ℕ.+ m)
                  ∎

lookup-env : ∀{n r}
             → (e : Env n)
             → (t : Type r)
             → (i : Fin n)
             → {_ : (r , t) ≡ lookup i e}
             → Type (just (Fin.toℕ i) R.+ r)
lookup-env {r = r} e t i with r
... | nothing = beef-up
                {const $ Type nothing}
                (λ{_ : ℕ} → T.suc {nothing})
                (Fin.toℕ i)
                {0}
                t
... | just y  = beef-up
                {λ(n : ℕ) → Type (just n)}
                (λ{n : ℕ} → T.suc {just n})
                (Fin.toℕ i)
                t

data Expr (Prim : Set) : ∀ {n r} → (tenv : Env n) → Type r → Set where

  prim-val : ∀ {n e}
             → Prim
             → Expr Prim {n} e prim

  prim-app : ∀ {n e a}
             → (Vec Prim a → Prim)
             → Vec Prim a
             → Expr Prim {n} e prim

  let-in   : ∀ {n r s}
             → {e  : Env n}
             → {t  : Type r}
             → {u  : Type s}
             → {nz : R.nonZero s}
             → Expr Prim {_} {r} e t
             → Expr Prim ((r , t) ∷ e) u
             → Expr Prim e (T.pred {s} {nz} u )

  iden     : ∀ {n r}
             → {e  : Env n}
             → {t  : Type r}
             → (i  : Fin n)
             → {eq : (r , t) ≡ lookup i e}
             → Expr Prim {n} e (lookup-env e t i {eq})

  ref      : ∀ {n s}
             → {e  : Env n}
             → {t  : Type s}
             → (i  : Fin n)
             → {eq : (s , t) ≡ lookup i e}
             → let r = just (Fin.toℕ i)
                   s' = r R.+ s
                   t' : Type s'
                   t' = lookup-env e t i {eq}
               in Expr Prim {n} e (pointer {s'} r {R.+-≤} t')

  load     : ∀ {n e r s le}
             → {t : Type s}
             → Expr Prim {n} e (pointer {s} r {le} t)
             → Expr Prim {n} e t

  store    : ∀ {n e r s le}
             → {t : Type s}
             → Expr Prim {n} e (pointer {s} r {le} t)
             → Expr Prim {n} e t
             → Expr Prim {n} e unit

  seq      : ∀ {n e r}
             → {t : Type r}
             → Expr Prim {n} e unit
             → Expr Prim {n} e t
             → Expr Prim {n} e t

Closed : (r : Region) → Set → Type r → Set
Closed _ Prim Type = Expr Prim [] Type
