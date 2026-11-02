module Type.SpineForm.KindingNormalization where

open import Prelude
open import Type.Context
open import Type.SpineForm
open import Type.SpineForm.Kinding
open import Type.SpineForm.KindingNormalForm
open import Type.SpineForm.Weakening
open import Type.SpineForm.Substitution


mutual
  η-expandTypeₛ : Kind → Typeₛ → Typeₛ
  η-expandTypeₛ ⋆         τₛ          = τₛ
  η-expandTypeₛ (κ ⇒ κ') (⟨ τₕ ⟩ τs) using var0 ← η-expandTypeₛ κ (⟨ var zero ⟩ [])
    = ⟨ lam κ (η-expandTypeₛ κ' (⟨ weakenTypeAtₕ zero τₕ ⟩ appendToSpine (weakenSpineAt zero τs) var0)) ⟩ []

  η-expandTypeₕ : Kind → Typeₕ → Typeₕ
  η-expandTypeₕ ⋆         τ = τ
  η-expandTypeₕ (κ ⇒ κ') τ using var0 ← η-expandTypeₛ κ (⟨ var zero ⟩ [])
    = lam κ (η-expandTypeₛ κ' (⟨ weakenTypeAtₕ zero τ ⟩ (var0 ∷ [])))

mutual
  normalizeTypeₛ : KindCtx → Typeₛ → Typeₛ
  normalizeTypeₛ Δ (⟨ τₕ ⟩ τs) = applyToSpine (⟨ normalizeTypeₕ Δ τₕ ⟩ []) (normalizeSpine Δ τs)

  normalizeTypeₕ : KindCtx → Typeₕ → Typeₕ
  normalizeTypeₕ Δ (var x)     with find Δ x
  ... | yes ⟨ κ , _ ⟩          = η-expandTypeₕ κ (var x)
  ... | no _                   = var x
  normalizeTypeₕ Δ (fun τ₁ τ₂) = fun (normalizeTypeₛ Δ τ₁) (normalizeTypeₛ Δ τ₂)
  normalizeTypeₕ Δ (lam κ τ)   = lam κ (normalizeTypeₛ (κ ∷ Δ) τ)
  normalizeTypeₕ Δ (all κ τ)   = all κ (normalizeTypeₛ (κ ∷ Δ) τ)

  normalizeSpine : KindCtx → Spine → Spine
  normalizeSpine _ []       = []
  normalizeSpine Δ (τ ∷ τs) = normalizeTypeₛ Δ τ ∷ normalizeSpine Δ τs


--------------------------------------------------------------------------------

η-expandKindingᵤ : Δ ⊢ᵤ τₛ ∶ κ → Δ ⊢ₙ η-expandTypeₛ κ τₛ ∶ κ
η-expandKindingᵤ {κ = ⋆}       p            = neu p
η-expandKindingᵤ {κ = κ ⇒ κ'} (⟨ pₓ ⟩ ps ) using var0 ← η-expandKindingᵤ (⟨ here ⟩ [])
  = lam (η-expandKindingᵤ (⟨ there pₓ ⟩ appendToKindingSpineₙ (weakenKindingSpineₙ {xᵣ = zero} ps) var0))

η-expandIndexing : Δ ∋ x ↦ κ → Δ ⊢ₙ ⟨ η-expandTypeₕ κ (var x) ⟩ [] ∶ κ
η-expandIndexing {κ = ⋆}       pₓ = neu (⟨ pₓ ⟩ [])
η-expandIndexing {κ = κ ⇒ κ'} pₓ using var0 ← η-expandKindingᵤ (⟨ here ⟩ [])
  = lam (η-expandKindingᵤ (⟨ there pₓ ⟩ (var0 ∷ [])))

mutual
  normalizeKindingₛ : Δ ⊢ₛ τₛ ∶ κ → Δ ⊢ₙ normalizeTypeₛ Δ τₛ ∶ κ
  normalizeKindingₛ (⟨ pₕ ⟩ ps) = applyToKindingSpineₙ' (normalizeKindingₕ pₕ) (normalizeKindingSpine ps)

  normalizeKindingₕ : Δ ⊢ₕ τₕ ∶ κ → Δ ⊢ₙ ⟨ normalizeTypeₕ Δ τₕ ⟩ [] ∶ κ
  normalizeKindingₕ (var pₓ)     rewrite lemma-varIndexExistsInCtx (var pₓ) .proj₂ = η-expandIndexing pₓ
  normalizeKindingₕ (fun p₁ p₂) = fun (normalizeKindingₛ p₁) (normalizeKindingₛ p₂)
  normalizeKindingₕ (lam p)     = lam (normalizeKindingₛ p)
  normalizeKindingₕ (all p)     = all (normalizeKindingₛ p)

  normalizeKindingSpine : Δ ∣ κ ⊢ₛ τsₛ ∶ κ' → Δ ∣ κ ⊢ₙ normalizeSpine Δ τsₛ ∶ κ'
  normalizeKindingSpine []       = []
  normalizeKindingSpine (p ∷ ps) = normalizeKindingₛ p ∷ normalizeKindingSpine ps