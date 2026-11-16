module Type.NormalForm.Substitution where

open import Prelude
open import Type.Context
open import Type.NormalForm
open import Type.NormalForm.Kinding
open import Type.NormalForm.Weakening

mutual
  substTypeₙ : Typeₙ → Index → Kind → Typeₙ → Typeₙ
  substTypeₙ (neu τ)     xₛ κₛ τₛ = substTypeᵤ τ xₛ κₛ τₛ
  substTypeₙ (fun τ₁ τ₂) xₛ κₛ τₛ = fun (substTypeₙ τ₁ xₛ κₛ τₛ) (substTypeₙ τ₂ xₛ κₛ τₛ)
  substTypeₙ (lam κ τ)   xₛ κₛ τₛ = lam κ (substTypeₙ τ (suc xₛ) κₛ (weakenTypeAtₙ zero τₛ))
  substTypeₙ (all κ τ)   xₛ κₛ τₛ = all κ (substTypeₙ τ (suc xₛ) κₛ (weakenTypeAtₙ zero τₛ))
  substTypeₙ stuck       _  _  _  = stuck

  substTypeᵤ : Typeᵤ → Index → Kind → Typeₙ → Typeₙ
  substTypeᵤ (⟨ x ⟩ τs) xₛ κₛ τₛ with x ≟ₓ xₛ
  ... | no ref   with ⟨ x' , _ ⟩ ← lemma-inequality-implies-weakening-exists ref = neu (⟨ x' ⟩ substSpineₙ τs xₛ κₛ τₛ)
  ... | yes refl = applyKindedTypeToSpineₙ κₛ τₛ (substSpineₙ τs xₛ κₛ τₛ)

  substSpineₙ : Spineₙ → Index → Kind → Typeₙ → Spineₙ
  substSpineₙ []       _  _  _  = []
  substSpineₙ (τ ∷ τs) xₛ κₛ τₛ = substTypeₙ τ xₛ κₛ τₛ ∷ substSpineₙ τs xₛ κₛ τₛ

  applyToKindedTypeₙ : Typeₙ → Kind → Typeₙ → Typeₙ
  applyToKindedTypeₙ (lam _ τ) κ τₛ = substTypeₙ τ zero κ τₛ
  applyToKindedTypeₙ (fun _ _) _ _  = stuck
  applyToKindedTypeₙ (all _ _) _ _  = stuck
  applyToKindedTypeₙ (neu _)   _ _  = stuck
  applyToKindedTypeₙ stuck     _ _  = stuck

  applyKindedTypeToSpineₙ : Kind → Typeₙ → Spineₙ → Typeₙ
  applyKindedTypeToSpineₙ _         τ []        = τ
  applyKindedTypeToSpineₙ ⋆         _ (_ ∷ _)   = stuck
  applyKindedTypeToSpineₙ (κ ⇒ κ') τ (τₛ ∷ τs) = applyKindedTypeToSpineₙ κ' (applyToKindedTypeₙ τ κ τₛ) τs

applyTypeₙ : Typeₙ → Typeₙ → Typeₙ
applyTypeₙ (lam κ τ) τₛ = substTypeₙ τ zero κ τₛ
applyTypeₙ (fun _ _) _  = stuck
applyTypeₙ (all _ _) _  = stuck
applyTypeₙ (neu _)   _  = stuck
applyTypeₙ stuck     _  = stuck

applyToSpineₙ : Typeₙ → Spineₙ → Typeₙ
applyToSpineₙ τ []        = τ
applyToSpineₙ τ (τₛ ∷ τs) = applyToSpineₙ (applyTypeₙ τ τₛ) τs


-- mutual
--   substTypeₙ' : Typeₙ → Index → Typeₙ → Typeₙ
--   substTypeₙ' (neu τ)     xₛ τₛ = substTypeᵤ' τ xₛ τₛ
--   substTypeₙ' (fun τ₁ τ₂) xₛ τₛ = fun (substTypeₙ' τ₁ xₛ τₛ) (substTypeₙ' τ₂ xₛ τₛ)
--   substTypeₙ' (lam κ τ)   xₛ τₛ = lam κ (substTypeₙ' τ (suc xₛ) (weakenTypeAtₙ zero τₛ))
--   substTypeₙ' (all κ τ)   xₛ τₛ = all κ (substTypeₙ' τ (suc xₛ) (weakenTypeAtₙ zero τₛ))
--   substTypeₙ' stuck       _  _ = stuck

--   substTypeᵤ' : Typeᵤ → Index → Typeₙ → Typeₙ
--   substTypeᵤ' (⟨ x ⟩ τs) xₛ τₛ with x ≟ₓ xₛ
--   ... | no ref with ⟨ x' , _ ⟩ ← lemma-inequality-implies-weakening-exists ref = neu (⟨ x' ⟩ substSpineₙ' τs xₛ τₛ)
--   ... | yes refl = applyToSpineₙ' τₛ (substSpineₙ' τs xₛ τₛ)

--   substSpineₙ' : Spineₙ → Index → Typeₙ → Spineₙ
--   substSpineₙ' []       _  _  = []
--   substSpineₙ' (τ ∷ τs) xₛ τₛ = substTypeₙ' τ xₛ τₛ ∷ substSpineₙ' τs xₛ τₛ

--   applyTypeₙ' : Typeₙ → Typeₙ → Typeₙ
--   applyTypeₙ' (lam _ τ) τₛ = substTypeₙ' τ zero τₛ
--   applyTypeₙ' (fun _ _) _  = stuck
--   applyTypeₙ' (all _ _) _  = stuck
--   applyTypeₙ' (neu _)   _  = stuck
--   applyTypeₙ' stuck     _  = stuck

--   applyToSpineₙ' : Typeₙ → Spineₙ → Typeₙ
--   applyToSpineₙ' τ         []        = τ
--   applyToSpineₙ' τ (τₛ ∷ τs) = applyToSpineₙ' (applyTypeₙ' τ τₛ) τs


--------------------------------------------------------------------------------

mutual
  substKindingₙ : Δ ⊢ₙ τₙ ∶ κ → Δ ∋ xₛ ↦ κₛ → Δ \\ xₛ ⊢ₙ τₙₛ ∶ κₛ → Δ \\ xₛ ⊢ₙ substTypeₙ τₙ xₛ κₛ τₙₛ ∶ κ
  substKindingₙ (neu p)     pₓ pₛ = substKindingᵤ p pₓ pₛ
  substKindingₙ (fun p₁ p₂) pₓ pₛ = fun (substKindingₙ p₁ pₓ pₛ) (substKindingₙ p₂ pₓ pₛ)
  substKindingₙ (all p)     pₓ pₛ = all (substKindingₙ p (there pₓ) (weakenKindingₙ {xᵣ = zero} pₛ))
  substKindingₙ (lam p)     pₓ pₛ = lam (substKindingₙ p (there pₓ) (weakenKindingₙ pₛ))

  substKindingᵤ : Δ ⊢ᵤ τᵤ ∶ ⋆ → Δ ∋ xₛ ↦ κₛ → Δ \\ xₛ ⊢ₙ τₙₛ ∶ κₛ → Δ \\ xₛ ⊢ₙ substTypeᵤ τᵤ xₛ κₛ τₙₛ ∶ ⋆
  substKindingᵤ {xₛ = xₛ} (⟨_⟩_ {x = x} pₓ ps) pₓₛ pₛ with x ≟ₓ xₛ
  ... | no ref   with ⟨ x' , refl ⟩ ← lemma-inequality-implies-weakening-exists ref = neu (⟨ strengthenIndexing pₓ ⟩ substKindingSpineₙ ps pₓₛ pₛ)
  ... | yes refl with refl ← lookupUniqueness pₓ pₓₛ = applyToKindingSpineₙ pₛ (substKindingSpineₙ ps pₓₛ pₛ)

  substKindingSpineₙ : Δ ∣ κ ⊢ₙ τs ∶ κ' → Δ ∋ xₛ ↦ κₛ → Δ \\ xₛ ⊢ₙ τₙₛ ∶ κₛ → Δ \\ xₛ ∣ κ ⊢ₙ substSpineₙ τs xₛ κₛ τₙₛ ∶ κ'
  substKindingSpineₙ []       _   _ = []
  substKindingSpineₙ (p ∷ ps) pₓₛ pₛ = substKindingₙ p pₓₛ pₛ ∷ substKindingSpineₙ ps pₓₛ pₛ

  applyToKindingSpineₙ : Δ ⊢ₙ τₙ ∶ κ → Δ ∣ κ ⊢ₙ τs ∶ κ' → Δ ⊢ₙ applyKindedTypeToSpineₙ κ τₙ τs ∶ κ'
  applyToKindingSpineₙ p       []       = p
  applyToKindingSpineₙ (lam p) (pₛ ∷ ps) = applyToKindingSpineₙ (substKindingₙ p here pₛ) ps
  
applyKindingₙ : Δ ⊢ₙ τₙ ∶ κ ⇒ κ' → Δ ⊢ₙ τₙₛ ∶ κ → Δ ⊢ₙ applyTypeₙ τₙ τₙₛ ∶ κ'
applyKindingₙ (lam p) pₛ = substKindingₙ p here pₛ

applyToKindingSpineₙ' : Δ ⊢ₙ τₙ ∶ κ → Δ ∣ κ ⊢ₙ τs ∶ κ' → Δ ⊢ₙ applyToSpineₙ τₙ τs ∶ κ'
applyToKindingSpineₙ' p []        = p
applyToKindingSpineₙ' p (pₛ ∷ ps) = applyToKindingSpineₙ' (applyKindingₙ p pₛ) ps