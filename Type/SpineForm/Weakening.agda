module Type.SpineForm.Weakening where

open import Prelude
open import Type.Context
open import Type.SpineForm
open import Type.SpineForm.Kinding
open import Type.SpineForm.KindingNormalForm


mutual
  weakenTypeAtₛ : Index → Typeₛ → Typeₛ
  weakenTypeAtₛ xᵣ (⟨ τ₁ ⟩ τ₂) = ⟨ weakenTypeAtₕ xᵣ τ₁ ⟩ weakenSpineAt xᵣ τ₂

  weakenTypeAtₕ : Index → Typeₕ → Typeₕ
  weakenTypeAtₕ xᵣ (var x)     = var (weakenIndexAt xᵣ x)
  weakenTypeAtₕ xᵣ (fun τ₁ τ₂) = fun (weakenTypeAtₛ xᵣ τ₁) (weakenTypeAtₛ xᵣ τ₂)
  weakenTypeAtₕ xᵣ (lam κ τ)   = lam κ (weakenTypeAtₛ (suc xᵣ) τ)
  weakenTypeAtₕ xᵣ (all κ τ)   = all κ (weakenTypeAtₛ (suc xᵣ) τ)

  weakenSpineAt : Index → Spine → Spine
  weakenSpineAt xᵣ []       = []
  weakenSpineAt xᵣ (τ ∷ τs) = weakenTypeAtₛ xᵣ τ ∷ weakenSpineAt xᵣ τs


--------------------------------------------------------------------------------

mutual
  weakenKindingAtₛ : (xᵣ : Index) → Δ \\ xᵣ ⊢ₛ τₛ ∶ κ → Δ ⊢ₛ weakenTypeAtₛ xᵣ τₛ ∶ κ
  weakenKindingAtₛ xᵣ (⟨ p ⟩ ps) = ⟨ weakenKindingAtₕ xᵣ p ⟩ weakenKindingSpineAt xᵣ ps

  weakenKindingAtₕ : (xᵣ : Index) → Δ \\ xᵣ ⊢ₕ τₕ ∶ κ → Δ ⊢ₕ weakenTypeAtₕ xᵣ τₕ ∶ κ
  weakenKindingAtₕ xᵣ (var pₓ)    = var (weakenIndexingAt xᵣ pₓ)
  weakenKindingAtₕ xᵣ (fun p₁ p₂) = fun (weakenKindingAtₛ xᵣ p₁) (weakenKindingAtₛ xᵣ p₂)
  weakenKindingAtₕ xᵣ (lam p)     = lam (weakenKindingAtₛ (suc xᵣ) p)
  weakenKindingAtₕ xᵣ (all p)     = all (weakenKindingAtₛ (suc xᵣ) p)

  weakenKindingSpineAt : (xᵣ : Index) → Δ \\ xᵣ ∣ κ ⊢ₛ τs ∶ κ' → Δ ∣ κ ⊢ₛ weakenSpineAt xᵣ τs ∶ κ'
  weakenKindingSpineAt xᵣ []       = []
  weakenKindingSpineAt xᵣ (p ∷ ps) = weakenKindingAtₛ xᵣ p ∷ weakenKindingSpineAt xᵣ ps


--------------------------------------------------------------------------------

mutual
  weakenKindingₙ : Δ \\ xᵣ ⊢ₙ τₛ ∶ κ → Δ ⊢ₙ weakenTypeAtₛ xᵣ τₛ ∶ κ
  weakenKindingₙ (neu p)     = neu (weakenKindingᵤ p)
  weakenKindingₙ (fun p₁ p₂) = fun (weakenKindingₙ p₁) (weakenKindingₙ p₂)
  weakenKindingₙ (all p)     = all (weakenKindingₙ p)
  weakenKindingₙ (lam p)     = lam (weakenKindingₙ p)

  weakenKindingᵤ : Δ \\ xᵣ ⊢ᵤ τₛ ∶ κ → Δ ⊢ᵤ weakenTypeAtₛ xᵣ τₛ ∶ κ
  weakenKindingᵤ {xᵣ = xᵣ} (⟨ pₓ ⟩ ps) = ⟨ weakenIndexingAt xᵣ pₓ ⟩ weakenKindingSpineₙ ps

  weakenKindingSpineₙ : Δ \\ xᵣ ∣ κ ⊢ₙ τs ∶ κ' → Δ ∣ κ ⊢ₙ weakenSpineAt xᵣ τs ∶ κ'
  weakenKindingSpineₙ []       = []
  weakenKindingSpineₙ (p ∷ ps) = weakenKindingₙ p ∷ weakenKindingSpineₙ ps