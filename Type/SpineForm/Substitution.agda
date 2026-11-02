module Type.SpineForm.Substitution where

open import Prelude
open import Type.Context
open import Type.SpineForm
open import Type.SpineForm.Kinding
open import Type.SpineForm.KindingNormalForm
open import Type.SpineForm.Weakening


mutual
  substTypeₛ : Typeₛ → Index → Kind → Typeₛ → Typeₛ
  substTypeₛ (⟨ var x ⟩ τs)     xₛ κₛ τₛ with x ≟ₓ xₛ
  ... | no ref   with ⟨ x' , _ ⟩ ← lemma-existsWeakenedIndex ref = ⟨ var x' ⟩ substSpine τs xₛ κₛ τₛ
  ... | yes refl = applyKindedTypeToSpine κₛ τₛ (substSpine τs xₛ κₛ τₛ)
  substTypeₛ (⟨ fun τ₁ τ₂ ⟩ τs) xₛ κₛ τₛ = ⟨ fun (substTypeₛ τ₁ xₛ κₛ τₛ) (substTypeₛ τ₂ xₛ κₛ τₛ) ⟩ substSpine τs xₛ κₛ τₛ
  substTypeₛ (⟨ lam κ τ ⟩ τs)   xₛ κₛ τₛ = ⟨ lam κ (substTypeₛ τ (suc xₛ) κₛ (weakenTypeAtₛ zero τₛ)) ⟩ substSpine τs xₛ κₛ τₛ
  substTypeₛ (⟨ all κ τ ⟩ τs)   xₛ κₛ τₛ = ⟨ all κ (substTypeₛ τ (suc xₛ) κₛ (weakenTypeAtₛ zero τₛ)) ⟩ substSpine τs xₛ κₛ τₛ

-- substTypeₕ : Typeₕ → Index → Kind → Typeₛ → Typeₛ
-- substTypeₕ (var x)     xₛ κₛ τₛ with x ≟ₓ xₛ
-- ... | no ref   with ⟨ x' , _ ⟩ ← lemma-existsWeakenedIndex ref = ⟨ var x' ⟩ []
-- ... | yes refl = τₛ
-- substTypeₕ (fun τ₁ τ₂) xₛ κₛ τₛ = ⟨ fun (substTypeₛ τ₁ xₛ κₛ τₛ) (substTypeₛ τ₂ xₛ κₛ τₛ) ⟩ []
-- substTypeₕ (lam κ τ)   xₛ κₛ τₛ = ⟨ lam κ (substTypeₛ τ (suc xₛ) κₛ (weakenTypeAtₛ zero τₛ)) ⟩ []
-- substTypeₕ (all κ τ)   xₛ κₛ τₛ = ⟨ all κ (substTypeₛ τ (suc xₛ) κₛ (weakenTypeAtₛ zero τₛ)) ⟩ []

  substSpine : Spine → Index → Kind → Typeₛ → Spine
  substSpine []       _  _ _  = []
  substSpine (τ ∷ τs) xᵣ κ τₛ = substTypeₛ τ xᵣ κ τₛ ∷ substSpine τs xᵣ κ τₛ

  -- apply : Kind → Typeₕ → Typeₛ → Typeₛ
  -- apply ⋆        τ           τₛ = ⟨ τ ⟩ (τₛ ∷ [])
  -- apply (κ ⇒ _) (lam _ τ)   τₛ = substTypeₛ τ zero κ τₛ
  -- apply (_ ⇒ _) (var x)     τₛ = ⟨ var x ⟩ (τₛ ∷ [])
  -- apply (_ ⇒ _) (fun τ₁ τ₂) τₛ = ⟨ fun τ₁ τ₂ ⟩ (τₛ ∷ [])
  -- apply (_ ⇒ _) (all κ τ)   τₛ = ⟨ all κ τ ⟩ (τₛ ∷ [])
  
  -- applyToSpine : Kind → Typeₕ → Spine → Typeₛ
  -- applyToSpine _         τ []        = ⟨ τ ⟩ []
  -- applyToSpine ⋆         τ (τₛ ∷ τs) = ⟨ τ ⟩ (τₛ ∷ τs)
  -- applyToSpine (κ ⇒ κ') τ (τₛ ∷ τs) with apply (κ ⇒ κ') τ τₛ
  -- ... | ⟨ τ' ⟩ []          = applyToSpine κ' τ' τs
  -- ... | ⟨ τ' ⟩ τs'@(_ ∷ _) = ⟨ τ' ⟩ concatSpines τs' τs

  -- applyToSpine : Kind → Typeₕ → Spine → Typeₛ
  -- applyToSpine _         τ []           = ⟨ τ ⟩ []
  -- applyToSpine ⋆         τ τs@(_ ∷ _)   = ⟨ τ ⟩ τs
  -- applyToSpine (κ ⇒ κ') τ τs@(τₛ ∷ τs') with τ
  -- ... | var x     = ⟨ var x ⟩ τs
  -- ... | fun τ₁ τ₂ = ⟨ fun τ₁ τ₂ ⟩ τs
  -- ... | all κ τ   = ⟨ all κ τ ⟩ τs
  -- ... | lam _ τ   with substTypeₛ τ zero κ τₛ
  -- ...   | ⟨ τ' ⟩ []          = applyToSpine κ' τ' τs'
  -- ...   | ⟨ τ' ⟩ τs'@(_ ∷ _) = ⟨ τ' ⟩ concatSpines τs' τs  
  
  -- applyToSpine' : Typeₕ → Spine → Typeₛ
  -- applyToSpine' τ []            = ⟨ τ ⟩ []
  -- applyToSpine' τ τs@(τₛ ∷ τs') with τ
  -- ... | var x     = ⟨ var x ⟩ τs
  -- ... | fun τ₁ τ₂ = ⟨ fun τ₁ τ₂ ⟩ τs
  -- ... | all κ τ   = ⟨ all κ τ ⟩ τs
  -- ... | lam κ τ   with substTypeₛ τ zero κ τₛ
  -- ...   | ⟨ τ' ⟩ []          = applyToSpine' τ' τs'
  -- ...   | ⟨ τ' ⟩ τs'@(_ ∷ _) = ⟨ τ' ⟩ concatSpines τs' τs

  -- applyToKindedTypeₛ : Typeₕ → Kind → Typeₛ → Typeₛ
  -- applyToKindedTypeₛ τₕ τₛ = {!   !}
  
  applyKindedTypeToSpine : Kind → Typeₛ → Spine → Typeₛ
  applyKindedTypeToSpine _         τ                 []            = τ
  applyKindedTypeToSpine _         (⟨ τₕ ⟩ (τ ∷ τs)) τs'           = ⟨ τₕ ⟩ (τ ∷ concatSpines τs τs')
  applyKindedTypeToSpine ⋆         (⟨ τₕ ⟩ [])       τs@(_ ∷ _)    = ⟨ τₕ ⟩ τs
  applyKindedTypeToSpine (κ ⇒ κ') (⟨ τₕ ⟩ [])       τs@(τₛ ∷ τs') with τₕ
  ... | var x     = ⟨ var x ⟩ τs
  ... | fun τ₁ τ₂ = ⟨ fun τ₁ τ₂ ⟩ τs
  ... | all κ τ   = ⟨ all κ τ ⟩ τs
  ... | lam _ τ   = applyKindedTypeToSpine κ' (substTypeₛ τ zero κ τₛ) τs'
  
applyToSpine : Typeₛ → Spine → Typeₛ
applyToSpine τ                 []            = τ
applyToSpine (⟨ τₕ ⟩ (τ ∷ τs)) τs'           = ⟨ τₕ ⟩ (τ ∷ concatSpines τs τs')
applyToSpine (⟨ τₕ ⟩ [])       τs@(τₛ ∷ τs') with τₕ
... | var x     = ⟨ var x ⟩ τs
... | fun τ₁ τ₂ = ⟨ fun τ₁ τ₂ ⟩ τs
... | all κ τ   = ⟨ all κ τ ⟩ τs
... | lam κ τ   = applyToSpine (substTypeₛ τ zero κ τₛ) τs'


--------------------------------------------------------------------------------

mutual
  substKindingₙ : ∀ {τₙ τₙₛ} → Δ ⊢ₙ τₙ ∶ κ → Δ ∋ xₛ ↦ κₛ → Δ \\ xₛ ⊢ₙ τₙₛ ∶ κₛ → Δ \\ xₛ ⊢ₙ substTypeₛ τₙ xₛ κₛ τₙₛ ∶ κ
  substKindingₙ (neu p)     pₓ pₛ = substKindingᵤ p pₓ pₛ
  substKindingₙ (fun p₁ p₂) pₓ pₛ = fun (substKindingₙ p₁ pₓ pₛ) (substKindingₙ p₂ pₓ pₛ)
  substKindingₙ (all p)     pₓ pₛ = all (substKindingₙ p (there pₓ) (weakenKindingₙ {xᵣ = zero} pₛ))
  substKindingₙ (lam p)     pₓ pₛ = lam (substKindingₙ p (there pₓ) (weakenKindingₙ pₛ))

  substKindingᵤ : ∀ {τᵤ τₙₛ} → Δ ⊢ᵤ τᵤ ∶ ⋆ → Δ ∋ xₛ ↦ κₛ → Δ \\ xₛ ⊢ₙ τₙₛ ∶ κₛ → Δ \\ xₛ ⊢ₙ substTypeₛ τᵤ xₛ κₛ τₙₛ ∶ ⋆
  substKindingᵤ {xₛ = xₛ} (⟨_⟩_ {x = x} pₓ ps) pₓₛ pₛ with x ≟ₓ xₛ
  ... | no ref   with ⟨ x' , refl ⟩ ← lemma-existsWeakenedIndex ref = neu (⟨ strengthenIndexingAt xₛ pₓ ⟩ substKindingSpineₙ ps pₓₛ pₛ)
  ... | yes refl with refl ← lookupUniqueness pₓ pₓₛ = applyToKindingSpineₙ pₛ (substKindingSpineₙ ps pₓₛ pₛ)

  substKindingSpineₙ : ∀ {τₙₛ} → Δ ∣ κ ⊢ₙ τs ∶ κ' → Δ ∋ xₛ ↦ κₛ → Δ \\ xₛ ⊢ₙ τₙₛ ∶ κₛ → Δ \\ xₛ ∣ κ ⊢ₙ substSpine τs xₛ κₛ τₙₛ ∶ κ'
  substKindingSpineₙ []       _   _ = []
  substKindingSpineₙ (p ∷ ps) pₓₛ pₛ = substKindingₙ p pₓₛ pₛ ∷ substKindingSpineₙ ps pₓₛ pₛ

  applyToKindingSpineₙ : ∀ {τₙ τs} → Δ ⊢ₙ τₙ ∶ κ → Δ ∣ κ ⊢ₙ τs ∶ κ' → Δ ⊢ₙ applyKindedTypeToSpine κ τₙ τs ∶ κ'
  applyToKindingSpineₙ p       []        = p
  applyToKindingSpineₙ (lam p) (pₛ ∷ ps) = applyToKindingSpineₙ (substKindingₙ p here pₛ) ps
  
applyToKindingSpineₙ' : ∀ {τₙ} → Δ ⊢ₙ τₙ ∶ κ → Δ ∣ κ ⊢ₙ τs ∶ κ' → Δ ⊢ₙ applyToSpine τₙ τs ∶ κ'
applyToKindingSpineₙ' p       []        = p
applyToKindingSpineₙ' (lam p) (pₛ ∷ ps) = applyToKindingSpineₙ' (substKindingₙ p here pₛ) ps