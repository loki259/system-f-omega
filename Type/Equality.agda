{-# OPTIONS --allow-unsolved-metas #-}

module Type.Equality where

open import Prelude
open import Type
open import Type.Context
open import Type.Kinding
open import Type.Substitution


infix 3 _⊢_≡ₜ_∶_
data _⊢_≡ₜ_∶_ (Δ : KindCtx) : Type → Type → Kind → Set where
  trefl : ∀ {τ κ}
    → Δ ⊢ τ ∶ κ
    → Δ ⊢ τ ≡ₜ τ ∶ κ
  tsym : ∀ {τ₁ τ₂ κ}
    → Δ ⊢ τ₁ ≡ₜ τ₂ ∶ κ
    → Δ ⊢ τ₂ ≡ₜ τ₁ ∶ κ
  ttrans : ∀ {τ₁ τ₂ τ₃}
    → Δ ⊢ τ₁ ≡ₜ τ₂ ∶ κ
    → Δ ⊢ τ₂ ≡ₜ τ₃ ∶ κ
    → Δ ⊢ τ₁ ≡ₜ τ₃ ∶ κ
  fun : ∀ {τ₁ τ₁' τ₂ τ₂'}
    → Δ ⊢ τ₁ ≡ₜ τ₁' ∶ ⋆
    → Δ ⊢ τ₂ ≡ₜ τ₂' ∶ ⋆
    → Δ ⊢ fun τ₁ τ₂ ≡ₜ fun τ₁' τ₂' ∶ ⋆
  all : ∀ {κ τ τ'}
    → κ ∷ Δ ⊢ τ ≡ₜ τ' ∶ ⋆
    → Δ ⊢ all κ τ ≡ₜ all κ τ' ∶ ⋆
  lam : ∀ {κ κ' τ τ'}
    → κ ∷ Δ ⊢ τ ≡ₜ τ' ∶ κ'
    → Δ ⊢ lam κ τ ≡ₜ lam κ τ' ∶ tfun κ κ'
  app : ∀ {κ κ' τ₁ τ₁' τ₂ τ₂'}
    → Δ ⊢ τ₁ ≡ₜ τ₁' ∶ tfun κ κ'
    → Δ ⊢ τ₂ ≡ₜ τ₂' ∶ κ
    → Δ ⊢ app τ₁ τ₂ ≡ₜ app τ₁' τ₂' ∶ κ'
  beta : ∀ {κ κ' τ τₛ}
    → Δ ⊢ app (lam κ τ) τₛ ∶ κ'
    → Δ ⊢ app (lam κ τ) τₛ ≡ₜ τ [ τₛ ] ∶ κ'
  eta : ∀ {κ κ' τ}
    → Δ ⊢ τ ∶ tfun κ κ'
    → Δ ⊢ τ ≡ₜ lam κ (app (weakenType τ) (var zero)) ∶ tfun κ κ'

extractKinding : Δ ⊢ τ ≡ₜ τ' ∶ κ → Δ ⊢ τ ∶ κ × Δ ⊢ τ' ∶ κ
extractKinding (trefl prf)                 = ⟨ prf , prf ⟩
extractKinding (tsym eq)                   = swap (extractKinding eq)
extractKinding (ttrans eq₁ eq₂)            = ⟨ extractKinding eq₁ .proj₁ , extractKinding eq₂ .proj₂ ⟩
extractKinding (beta (app (lam prf) prfₛ)) = ⟨ app (lam prf) prfₛ , substKindingHere prf prfₛ ⟩
extractKinding (eta prf)                   = ⟨ prf , lam (app (weakenKinding prf) (var here)) ⟩
extractKinding (fun eq₁ eq₂)               = Σ-zip fun fun (extractKinding eq₁) (extractKinding eq₂)
extractKinding (app eq₁ eq₂)               = Σ-zip app app (extractKinding eq₁) (extractKinding eq₂)
extractKinding (all eq)                    = Σ-map all all (extractKinding eq)
extractKinding (lam eq)                    = Σ-map lam lam (extractKinding eq)