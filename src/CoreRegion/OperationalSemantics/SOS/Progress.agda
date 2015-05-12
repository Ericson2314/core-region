module CoreRegion.OperationalSemantics.SOS.Progress (Prim : Set) where

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

import Data.Fin
open Data.Fin using (Fin)

open import Data.Vec
open import Data.List
open import Data.Sum
open import Data.Maybe

open import Relation.Nullary
open import Relation.Unary
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

open import CoreRegion.OperationalSemantics.SOS.Types Prim as CFG

private instance vecFunctor : ∀ {l n} → RawFunctor {l} (flip Vec n)
vecFunctor = RawApplicative.rawFunctor Data.Vec.applicative

private instance maybeFunctor = Data.Maybe.functor


private
  module D where
    import Level as L
    data Di {a b} (A : Set a) (B : Set b) : Set (a L.⊔ b) where
      di< : ( a :   A) (¬b : ¬ B) → Di A B
      di> : (¬a : ¬ A) ( b :   B) → Di A B

    promote : {A B C : Set} → ¬ A → Di B C → Tri A B C
    promote ¬a (di<  b ¬c) = tri≈ ¬a b ¬c
    promote ¬a (di> ¬b  c) = tri> ¬a ¬b c

    proj₁ : {A B : Set} → Di A B → Relation.Nullary.Dec A
    proj₁ (di< a ¬b) = yes a
    proj₁ (di> ¬a b) = no ¬a

    proj₂ : {A B : Set} → Di A B → Relation.Nullary.Dec A
    proj₂ (di< a ¬b) = yes a
    proj₂ (di> ¬a b) = no ¬a

  elim : {A B : Set} → (A ⊎ B) → ¬ A → ¬ B → ⊥
  elim (inj₁ x) y _ = y x
  elim (inj₂ x) _ y = y x
    
open D public

open import Data.Product

mutual
  progress : ∀ {n r e t}
             → (c : Config {n} {r} e t)
             → {_ : isGood c}
             → Tri (isValue c) (isRedex c) (isContext c)
  progress (value _) = tri< tt id id
  progress (expr exp) {inj₁ x} = tri< x (λ _ → x) (λ _ → x)
  progress (expr exp) {inj₂ x} = promote ¬V (progress' exp {x})
    where ¬V : ¬ isValue (expr exp)
          ¬V = λ()
          
  progress' : ∀ {n r e t}
             → (c : Expr Config {n} {r} e t)
             → {_ : Redex c ⊎ Context c}
             → Di (Redex c) (Context c)
  progress' (prim-val _) = di< tt id
  progress' (prim-app x₁ args) = {!!}
  progress' (let-in x y) = {!!}
  progress' (iden i) = di< tt id
  progress' (ref i) = di< tt id
  progress' (load x) = {!!}
  progress' (store (CFG.value x) (CFG.value x₁)) = di< tt (λ z → z)
  progress' (store (CFG.value x) (CFG.expr x₁)) = {!!}
  progress' (store (CFG.expr x) (CFG.value x₁)) = {!!}
  progress' (store (CFG.expr x) (CFG.expr x₁)) = {!!}
  progress' (seq (value x) (value y)) = di< tt (λ z → z)
  progress' (seq (expr x) (expr y)) = {!!}
  progress' (seq (value x) (expr y)) = {!!}
  progress' (seq (expr x) (value y)) {ttl} = di< ⊥' ¬C
      where ¬R : ¬ Redex (seq (expr x) (value y))
            ¬R = λ()
            ¬C : ¬ Context (seq (expr x) (value y))
            ¬C = λ()
            ⊥' : ⊥
            ⊥' = elim ttl (λ()) (λ())
