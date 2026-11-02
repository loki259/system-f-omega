module Type.NormalForm.Weakening where

open import Prelude
open import Type.NormalForm
open import Type.NormalForm.Kinding
open import Type.Context


mutual
  weakenTypeAtₙ : Index → Typeₙ → Typeₙ
  weakenTypeAtₙ xᵣ (neu τᵤ)      = neu (weakenTypeAtᵤ xᵣ τᵤ)
  weakenTypeAtₙ xᵣ (fun τₙ₁ τₙ₂) = fun (weakenTypeAtₙ xᵣ τₙ₁) (weakenTypeAtₙ xᵣ τₙ₂)
  weakenTypeAtₙ xᵣ (lam κ τₙ)    = lam κ (weakenTypeAtₙ (suc xᵣ) τₙ)
  weakenTypeAtₙ xᵣ (all κ τₙ)    = all κ (weakenTypeAtₙ (suc xᵣ) τₙ)
  weakenTypeAtₙ _  stuck         = stuck
  
  weakenTypeAtᵤ : Index → Typeᵤ → Typeᵤ
  weakenTypeAtᵤ xᵣ (⟨ x ⟩ τs) = ⟨ weakenIndexAt xᵣ x ⟩ weakenSpineAtₙ xᵣ τs 

  weakenSpineAtₙ : Index → Spineₙ → Spineₙ
  weakenSpineAtₙ xᵣ []        = []
  weakenSpineAtₙ xᵣ (τₙ ∷ τs) = weakenTypeAtₙ xᵣ τₙ ∷ weakenSpineAtₙ xᵣ τs


--------------------------------------------------------------------------------

mutual
  weakenKindingₙ : Δ \\ xᵣ ⊢ₙ τₙ ∶ κ → Δ ⊢ₙ weakenTypeAtₙ xᵣ τₙ ∶ κ
  weakenKindingₙ (neu p)     = neu (weakenKindingᵤ p)
  weakenKindingₙ (fun p₁ p₂) = fun (weakenKindingₙ p₁) (weakenKindingₙ p₂)
  weakenKindingₙ (all p)     = all (weakenKindingₙ p)
  weakenKindingₙ (lam p)     = lam (weakenKindingₙ p)

  weakenKindingᵤ : Δ \\ xᵣ ⊢ᵤ τᵤ ∶ κ → Δ ⊢ᵤ weakenTypeAtᵤ xᵣ τᵤ ∶ κ
  weakenKindingᵤ (⟨ pₓ ⟩ ps) = ⟨ weakenIndexing pₓ ⟩ weakenKindingSpineₙ ps

  weakenKindingSpineₙ : Δ \\ xᵣ ∣ κ ⊢ₙ τs ∶ κ' → Δ ∣ κ ⊢ₙ weakenSpineAtₙ xᵣ τs ∶ κ'
  weakenKindingSpineₙ []       = []
  weakenKindingSpineₙ (p ∷ ps) = weakenKindingₙ p ∷ weakenKindingSpineₙ ps