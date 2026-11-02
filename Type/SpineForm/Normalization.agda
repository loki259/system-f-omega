module Type.SpineForm.Normalization where

open import Prelude
open import Type.Context
open import Type.SpineForm renaming (⟨_⟩_ to app)
open import Type.SpineForm.Kinding renaming (⟨_⟩_ to app)
open import Type.NormalForm
open import Type.NormalForm.Kinding
open import Type.NormalForm.Weakening
open import Type.NormalForm.Substitution


η-expandTypeᵤ : Kind → Typeᵤ → Typeₙ
η-expandTypeᵤ ⋆         τᵤ         = neu τᵤ
η-expandTypeᵤ (κ ⇒ κ') (⟨ x ⟩ τs) using var0 ← η-expandTypeᵤ κ (⟨ zero ⟩ [])
  = lam κ (η-expandTypeᵤ κ' (⟨ suc x ⟩ appendToSpineₙ (weakenSpineAtₙ zero τs) var0))

mutual
  normalizeTypeₛ : KindCtx → Typeₛ → Typeₙ
  normalizeTypeₛ Δ (app τₕ τs) = applyToSpineₙ (normalizeTypeₕ Δ τₕ) (normalizeSpine Δ τs)

  normalizeTypeₕ : KindCtx → Typeₕ → Typeₙ
  normalizeTypeₕ Δ (var x)     with find Δ x
  ... | yes ⟨ κ , _ ⟩          = η-expandTypeᵤ κ (⟨ x ⟩ [])
  ... | no _                   = stuck
  normalizeTypeₕ Δ (fun τ₁ τ₂) = fun (normalizeTypeₛ Δ τ₁) (normalizeTypeₛ Δ τ₂)
  normalizeTypeₕ Δ (lam κ τ)   = lam κ (normalizeTypeₛ (κ ∷ Δ) τ)
  normalizeTypeₕ Δ (all κ τ)   = all κ (normalizeTypeₛ (κ ∷ Δ) τ)

  normalizeSpine : KindCtx → Spine → Spineₙ
  normalizeSpine _ []       = []
  normalizeSpine Δ (τ ∷ τs) = normalizeTypeₛ Δ τ ∷ normalizeSpine Δ τs


--------------------------------------------------------------------------------
  
η-expandKindingᵤ : Δ ⊢ᵤ τᵤ ∶ κ → Δ ⊢ₙ η-expandTypeᵤ κ τᵤ ∶ κ
η-expandKindingᵤ {κ = ⋆}       p            = neu p
η-expandKindingᵤ {κ = κ ⇒ κ'} (⟨ pₓ ⟩ ps ) using var0 ← η-expandKindingᵤ (⟨ here ⟩ [])
  = lam (η-expandKindingᵤ (⟨ there pₓ ⟩ appendToKindingSpineₙ (weakenKindingSpineₙ {xᵣ = zero} ps) var0))

mutual
  normalizeKindingₛ : Δ ⊢ₛ τₛ ∶ κ → Δ ⊢ₙ normalizeTypeₛ Δ τₛ ∶ κ
  normalizeKindingₛ (app pₕ ps) = applyToKindingSpineₙ' (normalizeKindingₕ pₕ) (normalizeKindingSpine ps)

  normalizeKindingₕ : Δ ⊢ₕ τₕ ∶ κ → Δ ⊢ₙ normalizeTypeₕ Δ τₕ ∶ κ
  normalizeKindingₕ (var p)     rewrite lemma-varIndexExistsInCtx (var p) .proj₂ = η-expandKindingᵤ (⟨ p ⟩ [])
  normalizeKindingₕ (fun p₁ p₂) = fun (normalizeKindingₛ p₁) (normalizeKindingₛ p₂)
  normalizeKindingₕ (lam p)     = lam (normalizeKindingₛ p)
  normalizeKindingₕ (all p)     = all (normalizeKindingₛ p)

  normalizeKindingSpine : Δ ∣ κ ⊢ₛ τsₛ ∶ κ' → Δ ∣ κ ⊢ₙ normalizeSpine Δ τsₛ ∶ κ'
  normalizeKindingSpine []       = []
  normalizeKindingSpine (p ∷ ps) = normalizeKindingₛ p ∷ normalizeKindingSpine ps