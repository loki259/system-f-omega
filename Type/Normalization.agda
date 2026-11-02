module Type.Normalization where

open import Prelude
open import Type
open import Type.Context
open import Type.Kinding
open import Type.NormalForm
open import Type.NormalForm.Kinding
open import Type.NormalForm.Weakening
open import Type.NormalForm.Substitution


η-expandTypeᵤ : Kind → Typeᵤ → Typeₙ
η-expandTypeᵤ ⋆         τᵤ         = neu τᵤ
η-expandTypeᵤ (κ ⇒ κ') (⟨ x ⟩ τs) using var0 ← η-expandTypeᵤ κ (⟨ zero ⟩ [])
  = lam κ (η-expandTypeᵤ κ' (⟨ suc x ⟩ appendToSpineₙ (weakenSpineAtₙ zero τs) var0))

normalizeType : KindCtx → Type → Typeₙ
normalizeType Δ (var x)     with find Δ x
... | yes ⟨ κ , _ ⟩         = η-expandTypeᵤ κ (⟨ x ⟩ [])
... | no _                  = stuck
normalizeType Δ (fun τ₁ τ₂) = fun (normalizeType Δ τ₁) (normalizeType Δ τ₂)
normalizeType Δ (app τ₁ τ₂) = applyTypeₙ (normalizeType Δ τ₁) (normalizeType Δ τ₂)
normalizeType Δ (lam κ τ)   = lam κ (normalizeType (κ ∷ Δ) τ)
normalizeType Δ (all κ τ)   = all κ (normalizeType (κ ∷ Δ) τ)


--------------------------------------------------------------------------------

η-expandKindingᵤ : Δ ⊢ᵤ τᵤ ∶ κ → Δ ⊢ₙ η-expandTypeᵤ κ τᵤ ∶ κ
η-expandKindingᵤ {κ = ⋆}       p            = neu p
η-expandKindingᵤ {κ = κ ⇒ κ'} (⟨ pₓ ⟩ ps ) using var0 ← η-expandKindingᵤ (⟨ here ⟩ [])
  = lam (η-expandKindingᵤ (⟨ there pₓ ⟩ appendToKindingSpineₙ (weakenKindingSpineₙ {xᵣ = zero} ps) var0))

lemma-varIndexExistsInCtx : Δ ⊢ var x ∶ κ → ∃[ p ] find Δ x ≡ yes ⟨ κ , p ⟩
lemma-varIndexExistsInCtx {Δ = Δ} {x = x} {κ = κ} (var p) with find Δ x
... | no ref         with () ← ref ⟨ κ , p ⟩
... | yes ⟨ _ , p' ⟩ with refl ← lookupUniqueness p p' = ⟨ p' , refl ⟩

normalizeKinding : Δ ⊢ τ ∶ κ → Δ ⊢ₙ normalizeType Δ τ ∶ κ
normalizeKinding (var p)     rewrite lemma-varIndexExistsInCtx (var p) .proj₂ = η-expandKindingᵤ (⟨ p ⟩ [])
normalizeKinding (app p₁ p₂) = applyKindingₙ (normalizeKinding p₁) (normalizeKinding p₂)
normalizeKinding (fun p₁ p₂) = fun (normalizeKinding p₁) (normalizeKinding p₂)
normalizeKinding (lam p)     = lam (normalizeKinding p)
normalizeKinding (all p)     = all (normalizeKinding p)