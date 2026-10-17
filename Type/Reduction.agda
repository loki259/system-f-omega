module Type.Reduction where

open import Prelude
open import Type
open import Type.Context
open import Type.Kinding
open import Type.Substitution


infix 3 _⊢_⟶w_∶_
data _⊢_⟶w_∶_ (Δ : KindCtx) : Type → Type → Kind → Set where
  beta : Δ ⊢ lam κ τ ∶ tfun κ κ' → Δ ⊢ τₛ ∶ κ → Δ ⊢ app (lam κ τ) τₛ ⟶w τ [ τₛ ] ∶ κ'
  appl : Δ ⊢ τ₁ ⟶w τ₁' ∶ κ → Δ ⊢ app τ₁ τ₂ ⟶w app τ₁' τ₂ ∶ κ