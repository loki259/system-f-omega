module Type.Normalization where

open import Prelude
open import Type
open import Type.Context
open import Type.Kinding
open import Type.Equality
open import Type.Substitution
open import Type.NormalForm
open import Type.NormalForm.Kinding
open import Type.NormalForm.Weakening
open import Type.NormalForm.Substitution
open import Type.NormalForm.Equality


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


mutual
  denormalizeTypeₙ : Typeₙ → Type
  denormalizeTypeₙ (neu τᵤ)      = denormalizeTypeᵤ τᵤ
  denormalizeTypeₙ (fun τₙ₁ τₙ₂) = fun (denormalizeTypeₙ τₙ₁) (denormalizeTypeₙ τₙ₂)
  denormalizeTypeₙ (lam κ τₙ)    = lam κ (denormalizeTypeₙ τₙ)
  denormalizeTypeₙ (all κ τₙ)    = all κ (denormalizeTypeₙ τₙ)
  denormalizeTypeₙ stuck         = app (var zero) (var zero)

  denormalizeTypeᵤ : Typeᵤ → Type
  denormalizeTypeᵤ (⟨ x ⟩ τs) = foldSpineₙ (var x) τs

  foldSpineₙ : Type → Spineₙ → Type
  foldSpineₙ τ []        = τ
  foldSpineₙ τ (τₙ ∷ τs) = foldSpineₙ (app τ (denormalizeTypeₙ τₙ)) τs

--------------------------------------------------------------------------------

η-expandKindingᵤ : Δ ⊢ᵤ τᵤ ∶ κ → Δ ⊢ₙ η-expandTypeᵤ κ τᵤ ∶ κ
η-expandKindingᵤ {κ = ⋆}       p            = neu p
η-expandKindingᵤ {κ = κ ⇒ κ'} (⟨ pₓ ⟩ ps ) using var0 ← η-expandKindingᵤ (⟨ here ⟩ [])
  = lam (η-expandKindingᵤ (⟨ there pₓ ⟩ appendToKindingSpineₙ (weakenKindingSpineₙ {xᵣ = zero} ps) var0))

lemma-varIndexExistsInCtx : Δ ∋ x ↦ κ → ∃[ p ] find Δ x ≡ yes ⟨ κ , p ⟩
lemma-varIndexExistsInCtx {Δ = Δ} {x = x} {κ = κ} pₓ with find Δ x
... | no ref          with () ← ref ⟨ κ , pₓ ⟩
... | yes ⟨ _ , pₓ' ⟩ with refl ← lookupUniqueness pₓ pₓ' = ⟨ pₓ' , refl ⟩

normalizeKinding : Δ ⊢ τ ∶ κ → Δ ⊢ₙ normalizeType Δ τ ∶ κ
normalizeKinding (var pₓ)    rewrite lemma-varIndexExistsInCtx pₓ .proj₂ = η-expandKindingᵤ (⟨ pₓ ⟩ [])
normalizeKinding (app p₁ p₂) = applyKindingₙ (normalizeKinding p₁) (normalizeKinding p₂)
normalizeKinding (fun p₁ p₂) = fun (normalizeKinding p₁) (normalizeKinding p₂)
normalizeKinding (lam p)     = lam (normalizeKinding p)
normalizeKinding (all p)     = all (normalizeKinding p)


mutual
  denormalizeKindingₙ : Δ ⊢ₙ τₙ ∶ κ → Δ ⊢ denormalizeTypeₙ τₙ ∶ κ
  denormalizeKindingₙ (neu pᵤ)      = denormalizeKindingᵤ pᵤ
  denormalizeKindingₙ (fun pₙ₁ pₙ₂) = fun (denormalizeKindingₙ pₙ₁) (denormalizeKindingₙ pₙ₂)
  denormalizeKindingₙ (all pₙ)      = all (denormalizeKindingₙ pₙ)
  denormalizeKindingₙ (lam pₙ)      = lam (denormalizeKindingₙ pₙ)

  denormalizeKindingᵤ : Δ ⊢ᵤ τᵤ ∶ κ → Δ ⊢ denormalizeTypeᵤ τᵤ ∶ κ
  denormalizeKindingᵤ (⟨ pₓ ⟩ ps) = foldKindingSpineₙ (var pₓ) ps

  foldKindingSpineₙ : Δ ⊢ τ ∶ κ → Δ ∣ κ ⊢ₙ τs ∶ κ' → Δ ⊢ foldSpineₙ τ τs ∶ κ'
  foldKindingSpineₙ p []        = p
  foldKindingSpineₙ p (pₙ ∷ ps) = foldKindingSpineₙ (app p (denormalizeKindingₙ pₙ)) ps


--------------------------------------------------------------------------------

normalizationSoundness : Δ ⊢ₙ τₙ ≡ₜ τₙ' ∶ κ → Δ ⊢ denormalizeTypeₙ τₙ ≡ₜ denormalizeTypeₙ τₙ' ∶ κ
normalizationSoundness (refl pₙ) = trefl (denormalizeKindingₙ pₙ)


mutual
  -- lemma-weakenTypeAtₙ-substTypeₙ-commutativity : Δ \\ suc xᵣ ⊢ₙ τₙ ∶ κ → Δ \\ suc xᵣ ∋ xₛ ↦ κₛ → Δ \\ weakenIndexAt (suc xᵣ) xₛ \\ xᵣ ⊢ₙ τₙₛ ∶ κₛ →  Δ \\ weakenIndexAt (suc xᵣ) xₛ ⊢ₙ weakenTypeAtₙ xᵣ (substTypeₙ τₙ xₛ κₛ τₙₛ) ≡ₜ substTypeₙ (weakenTypeAtₙ (suc xᵣ) τₙ) (weakenIndexAt (suc xᵣ) xₛ) κₛ (weakenTypeAtₙ xᵣ τₙₛ) ∶ κ
  lemma-weakenTypeAtₙ-substTypeₙ-commutativity : xₛ ≤ xᵣ → Δ \\ weakenIndexAt xₛ xᵣ ⊢ₙ τₙ ∶ κ → Δ \\ weakenIndexAt xₛ xᵣ ∋ xₛ ↦ κₛ → Δ \\ weakenIndexAt xₛ xᵣ \\ xₛ ⊢ₙ τₙₛ ∶ κₛ →  Δ \\ xₛ ⊢ₙ weakenTypeAtₙ xᵣ (substTypeₙ τₙ xₛ κₛ τₙₛ) ≡ₜ substTypeₙ (weakenTypeAtₙ (weakenIndexAt xₛ xᵣ) τₙ) (weakenIndexAt (weakenIndexAt xₛ xᵣ) xₛ) κₛ (weakenTypeAtₙ xᵣ τₙₛ) ∶ κ
  lemma-weakenTypeAtₙ-substTypeₙ-commutativity {Δ = Δ} xₛ≤xᵣ (neu pᵤ) pₓₛ pₛ = lemma-weakenTypeAtₙ-substTypeᵤ-commutativity {Δ = Δ} xₛ≤xᵣ pᵤ pₓₛ pₛ
  lemma-weakenTypeAtₙ-substTypeₙ-commutativity {Δ = Δ} xₛ≤xᵣ (fun p₁ p₂) pₓₛ pₛ
    rewrite extract≡ (lemma-weakenTypeAtₙ-substTypeₙ-commutativity {Δ = Δ} xₛ≤xᵣ p₁ pₓₛ pₛ)
    rewrite extract≡ (lemma-weakenTypeAtₙ-substTypeₙ-commutativity {Δ = Δ} xₛ≤xᵣ p₂ pₓₛ pₛ)
    = refl (fun {! substKindingₙ {Δ = Δ} (weakenKindingₙ p₁) {! weakenIndexing pₓₛ !} (weakenKindingₙ pₛ) !} {! substKindingₙ {Δ = Δ} (weakenKindingₙ p₂) (weakenIndexing pₓₛ) (weakenKindingₙ pₛ) !})
  lemma-weakenTypeAtₙ-substTypeₙ-commutativity {xₛ = xₛ} {xᵣ = xᵣ} {Δ = Δ} xₛ≤xᵣ (all {κ = κ} p) pₓₛ pₛ
    rewrite extract≡ (lemma-weakenTypeAtₙ-substTypeₙ-commutativity {Δ = κ ∷ Δ} (s≤s xₛ≤xᵣ) p (weakenIndexing {xᵣ = zero} pₓₛ) (weakenKindingₙ {xᵣ = zero} pₛ))
    rewrite lemma-weakenTypeAtₙ-commutativity {xᵣ' = xᵣ} pₛ z≤n
    = refl (all {! substKindingₙ {Δ = κ ∷ Δ} (weakenKindingₙ p) (there (weakenIndexing pₓₛ)) (weakenKindingₙ (weakenKindingₙ pₛ))!})
  lemma-weakenTypeAtₙ-substTypeₙ-commutativity {xₛ = xₛ} {xᵣ = xᵣ} {Δ = Δ} xₛ≤xᵣ (lam {κ = κ} p) pₓₛ pₛ
    rewrite extract≡ (lemma-weakenTypeAtₙ-substTypeₙ-commutativity {Δ = κ ∷ Δ} (s≤s xₛ≤xᵣ) p (weakenIndexing {xᵣ = zero} pₓₛ) (weakenKindingₙ {xᵣ = zero} pₛ))
    rewrite lemma-weakenTypeAtₙ-commutativity {xᵣ' = xᵣ} pₛ z≤n
    = refl (lam {! substKindingₙ {Δ = κ ∷ Δ} (weakenKindingₙ p) (there (weakenIndexing pₓₛ)) (weakenKindingₙ (weakenKindingₙ pₛ)) !})

  lemma-weakenTypeAtₙ-substTypeᵤ-commutativity : xₛ ≤ xᵣ → Δ \\ weakenIndexAt xₛ xᵣ ⊢ᵤ τᵤ ∶ κ → Δ \\ weakenIndexAt xₛ xᵣ ∋ xₛ ↦ κₛ → Δ \\ weakenIndexAt xₛ xᵣ \\ xₛ ⊢ₙ τₙₛ ∶ κₛ →  Δ \\ xₛ ⊢ₙ weakenTypeAtₙ xᵣ (substTypeᵤ τᵤ xₛ κₛ τₙₛ) ≡ₜ substTypeᵤ (weakenTypeAtᵤ (weakenIndexAt xₛ xᵣ) τᵤ) (weakenIndexAt (weakenIndexAt xₛ xᵣ) xₛ) κₛ (weakenTypeAtₙ xᵣ τₙₛ) ∶ κ
  lemma-weakenTypeAtₙ-substTypeᵤ-commutativity {xₛ = xₛ} {xᵣ = xᵣ} {Δ = Δ} xₛ≤xᵣ (⟨_⟩_ {x = x} pₓ ps) pₓₛ pₛ with x ≟ₓ xₛ | weakenIndexAt (weakenIndexAt xₛ xᵣ) x ≟ₓ weakenIndexAt (weakenIndexAt xₛ xᵣ) xₛ
  ... | no ref   | no ref'  with ⟨ x' , refl ⟩ ← lemma-inequality-implies-weakening-exists ref | ⟨ x'' , eq ⟩ ← lemma-inequality-implies-weakening-exists ref' = {!   !}
  ... | no ref   | yes eq   with () ← ref (lemma-weakenIndexAt-injectivity eq)
  ... | yes refl | no ref   with () ← ref (cong (weakenIndexAt (weakenIndexAt xₛ xᵣ)) {x = x} refl)
  ... | yes refl | yes refl with refl ← lookupUniqueness pₓ pₓₛ
    with ps' ← substKindingSpineₙ ps pₓₛ pₛ
    using original_pₛ ← pₛ
    rewrite sym (lemma-\\-commutativity' {x = xₛ} {x' = xᵣ} {Ψ = Δ} xₛ≤xᵣ)
    rewrite extract≡ (lemma-weakenTypeAtₙ-applyKindedTypeToSpineₙ-commutativity {Δ = Δ \\ xₛ} pₛ ps')
    rewrite extract≡fromSpineEq (lemma-weakenSpineAtₙ-substSpineₙ-commutativity {Δ = Δ} xₛ≤xᵣ ps pₓₛ original_pₛ)
    = refl {!   !}

  lemma-weakenSpineAtₙ-substSpineₙ-commutativity : xₛ ≤ xᵣ → Δ \\ weakenIndexAt xₛ xᵣ ∣ κ ⊢ₙ τs ∶ κ' → Δ \\ weakenIndexAt xₛ xᵣ ∋ xₛ ↦ κₛ → Δ \\ weakenIndexAt xₛ xᵣ \\ xₛ ⊢ₙ τₙₛ ∶ κₛ →  Δ \\ xₛ ∣ κ ⊢ₙ weakenSpineAtₙ xᵣ (substSpineₙ τs xₛ κₛ τₙₛ) ≡ₜ substSpineₙ (weakenSpineAtₙ (weakenIndexAt xₛ xᵣ) τs) (weakenIndexAt (weakenIndexAt xₛ xᵣ) xₛ) κₛ (weakenTypeAtₙ xᵣ τₙₛ) ∶ κ'
  lemma-weakenSpineAtₙ-substSpineₙ-commutativity         _     []       _   _  = refl []
  lemma-weakenSpineAtₙ-substSpineₙ-commutativity {Δ = Δ} xₛ≤xᵣ (p ∷ ps) pₓₛ pₛ
    rewrite extract≡ (lemma-weakenTypeAtₙ-substTypeₙ-commutativity {Δ = Δ} xₛ≤xᵣ p pₓₛ pₛ)
    rewrite extract≡fromSpineEq (lemma-weakenSpineAtₙ-substSpineₙ-commutativity {Δ = Δ} xₛ≤xᵣ ps pₓₛ pₛ)
    = refl {!   !}

  lemma-weakenTypeAtₙ-applyKindedTypeToSpineₙ-commutativity : Δ \\ xᵣ ⊢ₙ τₙ ∶ κ → Δ \\ xᵣ ∣ κ ⊢ₙ τs ∶ κ' → Δ ⊢ₙ weakenTypeAtₙ xᵣ (applyKindedTypeToSpineₙ κ τₙ τs) ≡ₜ applyKindedTypeToSpineₙ κ (weakenTypeAtₙ xᵣ τₙ) (weakenSpineAtₙ xᵣ τs) ∶ κ'
  lemma-weakenTypeAtₙ-applyKindedTypeToSpineₙ-commutativity {Δ = Δ} p       []       = refl (weakenKindingₙ p)
  lemma-weakenTypeAtₙ-applyKindedTypeToSpineₙ-commutativity {Δ = Δ} (lam {κ = κ} p) (pₛ ∷ ps)
    rewrite extract≡ (lemma-weakenTypeAtₙ-applyKindedTypeToSpineₙ-commutativity {Δ = Δ} (substKindingₙ p here pₛ) ps)
    rewrite extract≡ (lemma-weakenTypeAtₙ-substTypeₙ-commutativity {Δ = κ ∷ Δ} z≤n p here pₛ)
    = refl {!   !}

lemma-weakenType-applyType-commutativity : Δ \\ xᵣ ⊢ₙ τₙ₁ ∶ κ ⇒ κ' → Δ \\ xᵣ ⊢ₙ τₙ₂ ∶ κ → Δ ⊢ₙ weakenTypeAtₙ xᵣ (applyTypeₙ τₙ₁ τₙ₂) ≡ₜ applyTypeₙ (weakenTypeAtₙ xᵣ τₙ₁) (weakenTypeAtₙ xᵣ τₙ₂) ∶ κ'
lemma-weakenType-applyType-commutativity {Δ = Δ} (lam {κ = κ} p) pₛ
  rewrite extract≡ (lemma-weakenTypeAtₙ-substTypeₙ-commutativity {Δ = κ ∷ Δ} z≤n p here pₛ)
  = refl {!   !}

lemma-weakenSpineₙ-appendToSpineₙ-commutativity : Δ \\ xᵣ ∣ κ ⊢ₙ τs ∶ κ' ⇒ κ'' →  Δ \\ xᵣ ⊢ₙ τₙ ∶ κ' → Δ ∣ κ ⊢ₙ weakenSpineAtₙ xᵣ (appendToSpineₙ τs τₙ) ≡ₜ appendToSpineₙ (weakenSpineAtₙ xᵣ τs) (weakenTypeAtₙ xᵣ τₙ) ∶ κ''
lemma-weakenSpineₙ-appendToSpineₙ-commutativity []       p = refl (weakenKindingₙ p ∷ [])
lemma-weakenSpineₙ-appendToSpineₙ-commutativity {Δ = ∆} {xᵣ = xᵣ} (p ∷ ps) p'
  rewrite extract≡fromSpineEq (lemma-weakenSpineₙ-appendToSpineₙ-commutativity {Δ = ∆} {xᵣ = xᵣ} ps p')
  = refl (weakenKindingₙ p ∷ appendToKindingSpineₙ (weakenKindingSpineₙ ps) (weakenKindingₙ p'))

lemma-weakenTypeAtₙ-η-expandTypeᵤ-commutativity : Δ \\ xᵣ ⊢ᵤ τᵤ ∶ κ → Δ ⊢ₙ weakenTypeAtₙ xᵣ (η-expandTypeᵤ κ τᵤ) ≡ₜ η-expandTypeᵤ κ (weakenTypeAtᵤ xᵣ τᵤ) ∶ κ
lemma-weakenTypeAtₙ-η-expandTypeᵤ-commutativity                   {κ = ⋆}       pᵤ = refl (neu (weakenKindingᵤ pᵤ))
lemma-weakenTypeAtₙ-η-expandTypeᵤ-commutativity {Δ = Δ} {xᵣ = xᵣ} {κ = κ ⇒ κ'} (⟨ pₓ ⟩ ps)
  rewrite extract≡ (lemma-weakenTypeAtₙ-η-expandTypeᵤ-commutativity {Δ = κ ∷ Δ} {xᵣ = suc xᵣ} (⟨ there pₓ ⟩ appendToKindingSpineₙ (weakenKindingSpineₙ {xᵣ = zero} ps) (η-expandKindingᵤ (⟨ here ⟩ []))))
  rewrite extract≡fromSpineEq (lemma-weakenSpineₙ-appendToSpineₙ-commutativity {Δ = κ ∷ Δ} {xᵣ = suc xᵣ} (weakenKindingSpineₙ {xᵣ = zero} ps) (η-expandKindingᵤ (⟨ here ⟩ [])))
  rewrite extract≡ (lemma-weakenTypeAtₙ-η-expandTypeᵤ-commutativity {Δ = κ ∷ Δ} {xᵣ = suc xᵣ} (⟨ here ⟩ []))
  rewrite lemma-weakenSpineAtₙ-commutativity {xᵣ' = xᵣ} ps z≤n
  = refl {!   !}

lemma-weakenType-normalizeType-commutativity : Δ \\ xᵣ ⊢ τ ∶ κ → Δ ⊢ₙ weakenTypeAtₙ xᵣ (normalizeType (Δ \\ xᵣ) τ) ≡ₜ normalizeType Δ (weakenTypeAt xᵣ τ) ∶ κ
lemma-weakenType-normalizeType-commutativity {Δ = Δ} {xᵣ = xᵣ} (var pₓ)
  rewrite lemma-varIndexExistsInCtx pₓ .proj₂
  rewrite lemma-varIndexExistsInCtx (weakenIndexing {Ψ = Δ} {xᵣ = xᵣ} pₓ) .proj₂
  rewrite extract≡ (lemma-weakenTypeAtₙ-η-expandTypeᵤ-commutativity {Δ = Δ} {xᵣ = xᵣ} (⟨ pₓ ⟩ []))
  = refl (η-expandKindingᵤ (⟨ weakenIndexing pₓ ⟩ []))
lemma-weakenType-normalizeType-commutativity {Δ = Δ} {xᵣ = xᵣ} (fun p₁ p₂)
  rewrite extract≡ (lemma-weakenType-normalizeType-commutativity {Δ = Δ} {xᵣ = xᵣ} p₁)
  rewrite extract≡ (lemma-weakenType-normalizeType-commutativity {Δ = Δ} {xᵣ = xᵣ} p₂)
  = refl (fun (normalizeKinding (weakenKinding p₁)) (normalizeKinding (weakenKinding p₂)))
lemma-weakenType-normalizeType-commutativity {Δ = Δ} {xᵣ = xᵣ} (all {κ = κ} p)
  rewrite extract≡ (lemma-weakenType-normalizeType-commutativity {Δ = κ ∷ Δ} {xᵣ = suc xᵣ} p)
  = refl (all (normalizeKinding (weakenKinding p)))
lemma-weakenType-normalizeType-commutativity {Δ = Δ} {xᵣ = xᵣ} (lam {κ = κ} p)
  rewrite extract≡ (lemma-weakenType-normalizeType-commutativity {Δ = κ ∷ Δ} {xᵣ = suc xᵣ} p)
  = refl (lam (normalizeKinding (weakenKinding p)))
lemma-weakenType-normalizeType-commutativity {Δ = Δ} {xᵣ = xᵣ} (app {τ₁ = τ₁} p₁ p₂)
  rewrite sym (extract≡ (lemma-weakenType-normalizeType-commutativity {Δ = Δ} p₁))
  rewrite sym (extract≡ (lemma-weakenType-normalizeType-commutativity {Δ = Δ} p₂))
  rewrite extract≡ (lemma-weakenType-applyType-commutativity {Δ = Δ} (normalizeKinding p₁) (normalizeKinding p₂))
  = refl (applyKindingₙ (weakenKindingₙ (normalizeKinding p₁)) (weakenKindingₙ (normalizeKinding p₂)))


lemma-substTypeₙ-η-expandTypeᵤ-composition₁ : Δ \\ xₛ ⊢ᵤ τᵤ ∶ κ → Δ \\ xₛ ⊢ₙ τₙₛ ∶ κₛ → Δ \\ xₛ ⊢ₙ substTypeₙ (η-expandTypeᵤ κ (weakenTypeAtᵤ xₛ τᵤ)) xₛ κₛ τₙₛ ≡ₜ η-expandTypeᵤ κ τᵤ ∶ κ
lemma-substTypeₙ-η-expandTypeᵤ-composition₁ {xₛ = xₛ} {κ = ⋆}       (⟨_⟩_ {x = x} pₓ ps) pₛ with weakenIndexAt xₛ x ≟ₓ xₛ
... | no ref with ⟨ x' , eq ⟩ ← lemma-inequality-implies-weakening-exists ref
             with refl ← lemma-weakenIndexAt-injectivity eq
             = {! refl (neu (⟨ strengthenIndexing pₓ ⟩ ps)) !}
... | yes eq with () ← lemma-weakening-implies-inequality (sym eq) refl
lemma-substTypeₙ-η-expandTypeᵤ-composition₁ {xₛ = xₛ} {κ = κ ⇒ κ'} (⟨_⟩_ {x = x} pₓ ps) pₛ = {!   !}

lemma-substTypeₙ-η-expandTypeᵤ-composition₂ : Δ ∋ xₛ ↦ κ → Δ \\ xₛ ⊢ₙ τₙₛ ∶ κ → Δ \\ xₛ ⊢ₙ substTypeₙ (η-expandTypeᵤ κ (⟨ xₛ ⟩ [])) xₛ κ τₙₛ ≡ₜ τₙₛ ∶ κ
lemma-substTypeₙ-η-expandTypeᵤ-composition₂ {xₛ = xₛ} {κ = ⋆}       pₓₛ pₛ with xₛ ≟ₓ xₛ
... | no ref   with () ← ref refl
... | yes refl = refl pₛ
lemma-substTypeₙ-η-expandTypeᵤ-composition₂ {xₛ = xₛ} {κ = κ ⇒ κ'} pₓₛ pₛ = {!   !}


mutual
  lemma-substTypeₙ-substTypeₙ-commutativity : Δ ⊢ₙ τₙ ∶ κ → Δ \\ xₛ ⊢ₙ τₙₛ ∶ κₛ → Δ \\ xₛ \\ xₛ' ⊢ₙ τₙₛ' ∶ κₛ' → xₛ ≤ xₛ' → Δ \\ xₛ \\ xₛ' ⊢ₙ substTypeₙ (substTypeₙ τₙ xₛ κₛ τₙₛ) xₛ' κₛ' τₙₛ' ≡ₜ substTypeₙ (substTypeₙ τₙ (weakenIndexAt xₛ xₛ') κₛ' (weakenTypeAtₙ xₛ τₙₛ')) xₛ κₛ (substTypeₙ τₙₛ xₛ' κₛ' τₙₛ') ∶ κ
  lemma-substTypeₙ-substTypeₙ-commutativity (neu pᵤ)    pₛ pₛ' xₛ≤xₛ' = lemma-substTypeₙ-substTypeᵤ-commutativity pᵤ pₛ pₛ' xₛ≤xₛ'
  lemma-substTypeₙ-substTypeₙ-commutativity (fun p₁ p₂) pₛ pₛ' xₛ≤xₛ' = {!   !}
  lemma-substTypeₙ-substTypeₙ-commutativity (all p)     pₛ pₛ' xₛ≤xₛ' = {!   !}
  lemma-substTypeₙ-substTypeₙ-commutativity (lam p)     pₛ pₛ' xₛ≤xₛ' = {!   !}
  
  lemma-substTypeₙ-substTypeᵤ-commutativity : Δ ⊢ᵤ τᵤ ∶ κ → Δ \\ xₛ ⊢ₙ τₙₛ ∶ κₛ → Δ \\ xₛ \\ xₛ' ⊢ₙ τₙₛ' ∶ κₛ' → xₛ ≤ xₛ' → Δ \\ xₛ \\ xₛ' ⊢ₙ substTypeₙ (substTypeᵤ τᵤ xₛ κₛ τₙₛ) xₛ' κₛ' τₙₛ' ≡ₜ substTypeₙ (substTypeᵤ τᵤ (weakenIndexAt xₛ xₛ') κₛ' (weakenTypeAtₙ xₛ τₙₛ')) xₛ κₛ (substTypeₙ τₙₛ xₛ' κₛ' τₙₛ') ∶ κ
  lemma-substTypeₙ-substTypeᵤ-commutativity {xₛ = xₛ} {xₛ' = xₛ'} (⟨_⟩_ {x = x} pₓ ps) pₛ pₛ' xₛ≤xₛ' with x ≟ₓ xₛ
  ... | no ref   with ⟨ x' , refl ⟩ ← lemma-inequality-implies-weakening-exists ref with x' ≟ₓ xₛ'
  ...   | no ref'  with ⟨ x'' , refl ⟩ ← lemma-inequality-implies-weakening-exists ref' = {!   !}
  ...   | yes refl with weakenIndexAt xₛ x' ≟ₓ weakenIndexAt xₛ x'
  ...     | no ref'' with () ← ref'' (lemma-weakenIndexAt-injectivity {xᵣ = xₛ} refl)
  ...     | yes refl = {!   !}
  -- ... | yes refl with xₛ ≟ₓ weakenIndexAt xₛ xₛ'
  -- ...   | no ref = {!   !}
  -- ...   | yes eq = {!   !}

lemma-substTypeₙ-applyTypeₙ-commutativity : Δ ⊢ₙ τₙ₁ ∶ κ ⇒ κ' → Δ ⊢ₙ τₙ₂ ∶ κ → Δ \\ xₛ ⊢ₙ τₙₛ ∶ κₛ → Δ \\ xₛ ⊢ₙ substTypeₙ (applyTypeₙ τₙ₁ τₙ₂) xₛ κₛ τₙₛ ≡ₜ applyTypeₙ (substTypeₙ τₙ₁ xₛ κₛ τₙₛ) (substTypeₙ τₙ₂ xₛ κₛ τₙₛ) ∶ κ'
lemma-substTypeₙ-applyTypeₙ-commutativity (lam p) pₛ pₛ' = lemma-substTypeₙ-substTypeₙ-commutativity p pₛ pₛ' z≤n

lemma-substType-normalizeType-commutativity : Δ ⊢ τ ∶ κ → Δ \\ xₛ ⊢ τₛ ∶ κₛ → Δ \\ xₛ ⊢ₙ substTypeₙ (normalizeType Δ τ) xₛ κₛ (normalizeType (Δ \\ xₛ) τₛ) ≡ₜ normalizeType (Δ \\ xₛ) (τ [ xₛ ↦ τₛ ]) ∶ κ
lemma-substType-normalizeType-commutativity {xₛ = xₛ} (var {x = x} pₓ) pₛ
  rewrite lemma-varIndexExistsInCtx pₓ .proj₂
  with x ≟ₓ xₛ
... | no ref   with ⟨ x' , refl ⟩ ← lemma-inequality-implies-weakening-exists ref rewrite lemma-varIndexExistsInCtx (strengthenIndexing pₓ) .proj₂ = {!   !}
... | yes refl = {!   !}
lemma-substType-normalizeType-commutativity (fun p₁ p₂) pₛ
  rewrite sym (extract≡ (lemma-substType-normalizeType-commutativity p₁ pₛ))
  rewrite sym (extract≡ (lemma-substType-normalizeType-commutativity p₂ pₛ))
  = refl {!   !}
lemma-substType-normalizeType-commutativity {Δ = Δ} {xₛ = xₛ} (all {κ = κ} p) pₛ
  rewrite sym (extract≡ (lemma-substType-normalizeType-commutativity {xₛ = suc xₛ} p (weakenKinding {xᵣ = zero} pₛ)))
  rewrite sym (extract≡ (lemma-weakenType-normalizeType-commutativity {Δ = κ ∷ (Δ \\ xₛ)} {xᵣ = zero} pₛ))
  = refl {!   !}
lemma-substType-normalizeType-commutativity {Δ = Δ} {xₛ = xₛ} (lam {κ = κ} p) pₛ
  rewrite sym (extract≡ (lemma-substType-normalizeType-commutativity {xₛ = suc xₛ} p (weakenKinding {xᵣ = zero} pₛ)))
  rewrite sym (extract≡ (lemma-weakenType-normalizeType-commutativity {Δ = κ ∷ (Δ \\ xₛ)} {xᵣ = zero} pₛ))
  = refl {!   !}
lemma-substType-normalizeType-commutativity {Δ = Δ} (app {τ₁ = τ₁} p₁ p₂) pₛ
  rewrite sym (extract≡ (lemma-substType-normalizeType-commutativity p₁ pₛ))
  rewrite sym (extract≡ (lemma-substType-normalizeType-commutativity p₂ pₛ))
--   with normalizeType Δ τ₁ | normalizeKinding p₁
-- ... | _ | lam p = {!   !}
  rewrite sym (extract≡ (lemma-substTypeₙ-applyTypeₙ-commutativity (normalizeKinding p₁) (normalizeKinding p₂) (normalizeKinding pₛ)))
  = refl {!   !}


mutual
  lemma-substTypeₙ-expansion : Δ \\ suc xₛ ⊢ₙ τₙ ∶ κ → Δ ∋ xₛ ↦ κₛ → Δ ∋ suc xₛ ↦ κₛ → Δ \\ xₛ ⊢ₙ τₙ ≡ₜ substTypeₙ (weakenTypeAtₙ (suc xₛ) τₙ) xₛ κₛ (η-expandTypeᵤ κₛ (⟨ xₛ ⟩ [])) ∶ κ
  lemma-substTypeₙ-expansion {Δ = Δ} {xₛ = xₛ} (neu pᵤ) pₓₛ pₓₛ' = lemma-substTypeᵤ-expansion pᵤ pₓₛ pₓₛ'
  lemma-substTypeₙ-expansion {xₛ = xₛ} (fun p₁ p₂) pₓₛ pₓₛ'
    rewrite sym (extract≡ (lemma-substTypeₙ-expansion {xₛ = xₛ} p₁ pₓₛ pₓₛ'))
    rewrite sym (extract≡ (lemma-substTypeₙ-expansion {xₛ = xₛ} p₂ pₓₛ pₓₛ'))
    rewrite lemma-\\-with-consecutive-indices pₓₛ pₓₛ'
    = refl (fun p₁ p₂)
  lemma-substTypeₙ-expansion {Δ = ∆} {xₛ = xₛ} (all {κ = κ} p) pₓₛ pₓₛ'
    rewrite extract≡ (lemma-weakenTypeAtₙ-η-expandTypeᵤ-commutativity {Δ = κ ∷ ∆} {xᵣ = zero} (⟨ pₓₛ ⟩ []))
    rewrite sym (extract≡ (lemma-substTypeₙ-expansion p (there pₓₛ) (there pₓₛ')))
    rewrite lemma-\\-with-consecutive-indices pₓₛ pₓₛ'
    = refl (all p)
  lemma-substTypeₙ-expansion {Δ = ∆} {xₛ = xₛ} (lam {κ = κ} p) pₓₛ pₓₛ'
    rewrite extract≡ (lemma-weakenTypeAtₙ-η-expandTypeᵤ-commutativity {Δ = κ ∷ ∆} {xᵣ = zero} (⟨ pₓₛ ⟩ []))
    rewrite sym (extract≡ (lemma-substTypeₙ-expansion p (there pₓₛ) (there pₓₛ')))
    rewrite lemma-\\-with-consecutive-indices pₓₛ pₓₛ'
    = refl (lam p)

  lemma-substTypeᵤ-expansion : Δ \\ suc xₛ ⊢ᵤ τᵤ ∶ ⋆ → Δ ∋ xₛ ↦ κₛ → Δ ∋ suc xₛ ↦ κₛ → Δ \\ xₛ ⊢ₙ neu τᵤ ≡ₜ substTypeᵤ (weakenTypeAtᵤ (suc xₛ) τᵤ) xₛ κₛ (η-expandTypeᵤ κₛ (⟨ xₛ ⟩ [])) ∶ ⋆
  lemma-substTypeᵤ-expansion {Δ = Δ} {xₛ = xₛ} (⟨_⟩_ {x = x} pₓ ps) pₓₛ pₓₛ' with weakenIndexAt (suc xₛ) x ≟ₓ xₛ
  ... | no ref with ⟨ x'' , eq ⟩ ← lemma-inequality-implies-weakening-exists ref
    rewrite sym (lemma-weakenIndexAt-with-consecutive-indices ref pₓₛ pₓₛ')
    rewrite lemma-weakenIndexAt-injectivity (sym eq)
    rewrite sym (extract≡fromSpineEq (lemma-substSpineₙ-expansion ps pₓₛ pₓₛ'))
    rewrite lemma-\\-with-consecutive-indices pₓₛ pₓₛ'
    = refl (neu (⟨ pₓ ⟩ ps))
  ... | yes eq with weakenIndexAt (suc xₛ) x | pₓₛ | pₓₛ' | eq
  ...   | _ | new_pₓₛ | new_pₓₛ' | refl -- with q ← lookupUniqueness (weakenIndexing {xᵣ = suc xₛ} pₓ) {! new_pₓₛ !}
    rewrite sym eq
    rewrite sym (extract≡fromSpineEq (lemma-substSpineₙ-expansion ps pₓₛ pₓₛ'))
    -- rewrite sym (extract≡ (lemma-applyKindedTypeToSpineₙ-expansion {!  ≤-reflexive eq !} pₓ ps {! pₓₛ !} {! pₓₛ' !}))
    = {!    !}

  lemma-substSpineₙ-expansion : Δ \\ suc xₛ ∣ κ ⊢ₙ τs ∶ κ' → Δ ∋ xₛ ↦ κₛ → Δ ∋ suc xₛ ↦ κₛ → Δ \\ xₛ ∣ κ ⊢ₙ τs ≡ₜ substSpineₙ (weakenSpineAtₙ (suc xₛ) τs) xₛ κₛ (η-expandTypeᵤ κₛ (⟨ xₛ ⟩ [])) ∶ κ'
  lemma-substSpineₙ-expansion []       _   _    = refl []
  lemma-substSpineₙ-expansion (p ∷ ps) pₓₛ pₓₛ'
    rewrite sym (extract≡ (lemma-substTypeₙ-expansion p pₓₛ pₓₛ'))
    rewrite sym (extract≡fromSpineEq (lemma-substSpineₙ-expansion ps pₓₛ pₓₛ'))
    rewrite lemma-\\-with-consecutive-indices pₓₛ pₓₛ'
    = refl (p ∷ ps)

  lemma-applyKindedTypeToSpineₙ-expansion : x ≤ xₛ → Δ \\ suc xₛ ∋ x ↦ κ → Δ \\ suc xₛ ∣ κ ⊢ₙ τs ∶ ⋆ → Δ ∋ xₛ ↦ κ → Δ ∋ suc xₛ ↦ κ → Δ \\ xₛ ⊢ₙ neu (⟨ x ⟩ τs) ≡ₜ applyKindedTypeToSpineₙ κ (η-expandTypeᵤ κ (⟨ weakenIndexAt (suc xₛ) x ⟩ [])) τs ∶ ⋆
  lemma-applyKindedTypeToSpineₙ-expansion x≤xₛ pₓ []       pₓₛ pₓₛ'
    rewrite lemma-weakenIndexAt-identity x≤xₛ
    rewrite lemma-\\-with-consecutive-indices pₓₛ pₓₛ'
    = refl (neu (⟨ pₓ ⟩ []))
  lemma-applyKindedTypeToSpineₙ-expansion x≤xₛ pₓ (p ∷ ps) pₓₛ pₓₛ'
    rewrite sym (extract≡ (lemma-substTypeₙ-expansion p pₓₛ pₓₛ'))
    -- rewrite sym (extract≡ (lemma-applyKindedTypeToSpineₙ-expansion pₓ ps pₓₛ pₓₛ'))
    = {!   !}

-- lemma-normal-eta-expansion' : Δ ⊢ τ ∶ κ ⇒ κ' → Δ ⊢ₙ normalizeType Δ τ ≡ₜ lam κ (applyTypeₙ (normalizeType (κ ∷ Δ) (weakenTypeAt 0 τ)) (η-expandTypeᵤ κ (⟨ 0 ⟩ []))) ∶ κ ⇒ κ'
-- lemma-normal-eta-expansion' = {!   !}

lemma-normal-eta-expansion : Δ ⊢ₙ τₙ ∶ κ ⇒ κ' → Δ ⊢ₙ τₙ ≡ₜ lam κ (applyTypeₙ (weakenTypeAtₙ zero τₙ) (η-expandTypeᵤ κ (⟨ zero ⟩ []))) ∶ κ ⇒ κ'
lemma-normal-eta-expansion {Δ = Δ} (lam {κ = κ} p)
  rewrite sym (extract≡ (lemma-substTypeₙ-expansion {Δ = κ ∷ κ ∷ Δ} p here (there here)))
  = refl (lam p)


normalizationCompleteness : Δ ⊢ τ ≡ₜ τ' ∶ κ → Δ ⊢ₙ normalizeType Δ τ ≡ₜ normalizeType Δ τ' ∶ κ
normalizationCompleteness (trefl p)        = refl (normalizeKinding p)
normalizationCompleteness (tsym eq)        = ≡ₜ-symₙ (normalizationCompleteness eq)
normalizationCompleteness (ttrans eq₁ eq₂) = ≡ₜ-transₙ (normalizationCompleteness eq₁) (normalizationCompleteness eq₂)
normalizationCompleteness {Δ = Δ} (fun {τ₁ = τ₁} {τ₂ = τ₂} eq₁ eq₂)
  with normalizeType Δ τ₁ | normalizeType Δ τ₂ | normalizationCompleteness eq₁ | normalizationCompleteness eq₂
... | _ | _ | refl pₙ₁ | refl pₙ₂ = refl (fun pₙ₁ pₙ₂)
normalizationCompleteness {Δ = Δ} (all {κ = κ} {τ = τ} eq)
  with normalizeType (κ ∷ Δ) τ | normalizationCompleteness eq
... | _ | refl pₙ = refl (all pₙ)
normalizationCompleteness {Δ = Δ} (lam {κ = κ} {τ = τ} eq)
  with normalizeType (κ ∷ Δ) τ | normalizationCompleteness eq
... | _ | refl pₙ = refl (lam pₙ)
normalizationCompleteness {Δ = Δ} (app {τ₁ = τ₁} {τ₂ = τ₂} eq₁ eq₂)
  with normalizeType Δ τ₁ | normalizeType Δ τ₂ | normalizationCompleteness eq₁ | normalizationCompleteness eq₂
... | _ | _ | refl pₙ₁ | refl pₙ₂ = refl (applyKindingₙ pₙ₁ pₙ₂)
normalizationCompleteness (beta (app (lam p) pₛ)) -- = lemma-substType-normalizeType-commutativity p pₛ
  rewrite sym (extract≡ (lemma-substType-normalizeType-commutativity {xₛ = zero} p pₛ))
  = refl (substKindingₙ (normalizeKinding p) here (normalizeKinding pₛ))
normalizationCompleteness {Δ = Δ} {τ = τ} {κ = κ ⇒ κ'} (eta p)
  rewrite sym (extract≡ (lemma-weakenType-normalizeType-commutativity {Δ = κ ∷ Δ} {xᵣ = zero} p))
  rewrite sym (extract≡ (lemma-normal-eta-expansion (normalizeKinding p)))
  = refl (normalizeKinding p)