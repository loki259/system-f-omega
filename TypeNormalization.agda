{-# OPTIONS --allow-unsolved-metas #-}

module TypeNormalization where

open import Prelude
open import Syntax
open import Context
open import Kinding
open import Typing

    
mutual
  infix 3 _⊢ₙ_∶_
  data _⊢ₙ_∶_ (Δ : KindCtx) : Typeₙ → Kind → Set where
    neu : ∀ {τ} → Δ ⊢ᵤ τ ∶ ⋆ → Δ ⊢ₙ neu τ ∶ ⋆
    fun : ∀ {τ τ'} → Δ ⊢ₙ τ ∶ ⋆ → Δ ⊢ₙ τ' ∶ ⋆ → Δ ⊢ₙ fun τ τ' ∶ ⋆
    all : ∀ {κ τ} → κ ∷ Δ ⊢ₙ τ ∶ ⋆ → Δ ⊢ₙ all κ τ ∶ ⋆
    lam : ∀ {κ κ' τ} → κ ∷ Δ ⊢ₙ τ ∶ κ' → Δ ⊢ₙ lam κ τ ∶ tfun κ κ'

  infix 3 _⊢ᵤ_∶_
  data _⊢ᵤ_∶_ (Δ : KindCtx) : Typeᵤ → Kind → Set where
    var : ∀ {x} → Δ ∋ x ↦ κ → Δ ⊢ᵤ var x ∶ κ
    app : ∀ {τ τ' κ κ'} → Δ ⊢ᵤ τ ∶ tfun κ κ' → Δ ⊢ₙ τ' ∶ κ → Δ ⊢ᵤ app τ τ' ∶ κ'


-- mutual
  -- renameTypeₙ : ∀ {Φ Ψ} → Renaming Φ Ψ → ∀ {τ κ} → Φ ⊢ₙ τ ∶ κ → ∃[ τ' ] Ψ ⊢ₙ τ' ∶ κ
  -- renameTypeₙ ρ (neu u)         = Σ-map₂ neu (renameTypeᵤ ρ u)
  -- renameTypeₙ ρ (lam prf)       = Σ-map (lam _) lam (renameTypeₙ (lift ρ) prf)
  -- renameTypeₙ ρ (fun prf₁ prf₂) = Σ-zip fun fun (renameTypeₙ ρ prf₁) (renameTypeₙ ρ prf₂)
  -- renameTypeₙ ρ (all prf)       = Σ-map (all _) all (renameTypeₙ (lift ρ) prf)

  -- renameTypeᵤ : ∀ {Φ Ψ} → Renaming Φ Ψ → ∀ {τ κ} → Φ ⊢ᵤ τ ∶ κ → ∃[ τ' ] Ψ ⊢ᵤ τ' ∶ κ
  -- renameTypeᵤ ρ (var prf)       = Σ-map var var (ρ prf)
  -- renameTypeᵤ ρ (app prf₁ prf₂) = Σ-zip app app (renameTypeᵤ ρ prf₁) (renameTypeₙ ρ prf₂)

-- weakenTypeₙ : ∀ {Φ κ κ' τ} → Φ ⊢ₙ τ ∶ κ → ∃[ τ' ] κ' ∷ Φ ⊢ₙ τ' ∶ κ
-- weakenTypeₙ = renameTypeₙ λ prf → -, there prf


-- renameTypeₙ-id : ∀ {Φ J} (A : Φ ⊢ᵤ J) → renameTypeₙ id A ≡ A
-- renameTypeₙ-comp : ∀ {Φ Ψ Θ} {ρ : Renaming Φ Ψ} {ρ' : Renaming Ψ Θ} {J} (A : Φ ⊢ₙ J)
--                  → renameTypeₙ (ρ' ◦ ρ) A ≡ renameTypeₙ ρ' (renameTypeₙ ρ A)

-- renameTypeᵤ-id : ∀ {Φ J} (A : Φ ⊢ᵤ J) → renameTypeᵤ id A ≡ A
-- renameTypeᵤ-comp : ∀ {Φ Ψ Θ}{ρ : Renaming Φ Ψ} {ρ' : Renaming Ψ Θ} {J} (A : Φ ⊢ᵤ J)
--                  → renameTypeᵤ (ρ' ◦ ρ) A ≡ renameTypeᵤ ρ' (renameTypeᵤ ρ A)


normalizeType : Type → Typeₙ
normalizeType = {!   !}

normalizeTyping : ∀ {Δ τ κ} → Δ ⊢ τ ∶ κ → Δ ⊢ₙ normalizeType τ ∶ κ
normalizeTyping = {!   !}