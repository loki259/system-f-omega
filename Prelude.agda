{-# OPTIONS --allow-unsolved-metas #-}

module Prelude where

open import Agda.Builtin.Nat public using (Nat; suc; zero)
open import Data.Bool public
open import Data.List public using (List; []; _∷_; map)
open import Relation.Nullary.Decidable public hiding (map)
open import Data.Product public hiding (map) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality public
open import Relation.Nullary.Negation public using (¬_)


Ctx : (T : Set) → Set
Ctx = List

data _∋_↦_ {A : Set} : Ctx A → Nat → A → Set where
  here  : ∀ {ctx a} → (a ∷ ctx) ∋ zero ↦ a
  there : ∀ {ctx x a b} → ctx ∋ x ↦ a → (b ∷ ctx) ∋ suc x ↦ a

-- data _∋_⦂_ {A : Set} : Ctx A → Nat → A → Set where
--   Z : ∀ {Γ x A} → (x ⦂ A ∷ Γ) ∋ x ⦂ A
--   S : ∀ {Γ x y A B} → x ≢ y → Γ ∋ x ⦂ A → (y ∷ Γ) ⦂ B ∋ x ⦂ A

lookup : ∀ {A x a} → (ctx : Ctx A) → ctx ∋ x ↦ a → A
lookup (a ∷ ctx) here        = a
lookup (_ ∷ ctx) (there prf) = lookup ctx prf

find : ∀ {A} → (ctx : Ctx A) → (x : Nat) → Dec (∃[ a ] ctx ∋ x ↦ a)
find []        x    = no λ ()
find (x ∷ ctx) zero = yes ⟨ x , here ⟩
find (x ∷ ctx) (suc x') with find ctx x'
... | no ref          = no λ { ⟨ a , there prf ⟩ → ref ⟨ a , prf ⟩}
... | yes ⟨ a , prf ⟩ = yes ⟨ a , there prf ⟩

case_of_ : ∀ {A B : Set} → A → (A → B) → B
case x of f = f x