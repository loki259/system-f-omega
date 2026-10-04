open import Data.Vec using (_∷_; lookup)
open import Syntax
open import Typing

module Normalization where

mutual
  infix 3 _⊢ₙ_∶_
  data _⊢ₙ_∶_ {m} (Δ : TypeCtx m) : Type m → Kind → Set where
    neu : ∀ {τ} → Δ ⊢ᵤ τ ∶ ⋆ → Δ ⊢ₙ τ ∶ ⋆
    fun : ∀ {τ τ'} → Δ ⊢ₙ τ ∶ ⋆ → Δ ⊢ₙ τ' ∶ ⋆ → Δ ⊢ₙ fun τ τ' ∶ ⋆
    all : ∀ {κ τ} → κ ∷ Δ ⊢ₙ τ ∶ ⋆ → Δ ⊢ₙ all κ τ ∶ ⋆
    lam : ∀ {κ κ' τ} → κ ∷ Δ ⊢ₙ τ ∶ κ' → Δ ⊢ₙ lam κ τ ∶ tfun κ κ'

  infix 3 _⊢ᵤ_∶_
  data _⊢ᵤ_∶_ {m} (Δ : TypeCtx m) : Type m → Kind → Set where
    var : ∀ {v} → Δ ⊢ᵤ var v ∶ lookup Δ v
    app : ∀ {τ τ' κ κ'} → Δ ⊢ᵤ τ ∶ tfun κ κ' → Δ ⊢ₙ τ' ∶ κ → Δ ⊢ᵤ app τ τ' ∶ κ'


normalizeTyping : ∀ {m τ τ' κ} → {Δ : TypeCtx m} → Δ ⊢ τ ∶ κ → Δ ⊢ₙ τ' ∶ κ
normalizeTyping = {!   !}