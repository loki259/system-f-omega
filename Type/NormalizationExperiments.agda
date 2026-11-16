module Type.NormalizationExperiments where

open import Prelude
open import Type
open import Type.Context
open import Type.Kinding
open import Type.Normalization
open import Type.NormalForm
open import Type.NormalForm.Kinding
open import Type.NormalForm.Weakening
open import Type.NormalForm.Substitution


--------------------------------------------------------------------------------
-- Idea: Only normalize and substitute well-formed types
--------------------------------------------------------------------------------
-- Instead of giving kind context to `normalizeType`, why not normalize only well-kinded types?
-- → Seems to work (see `normalizeWellKindedType`) because kinding for ordinary types is already defined/derivable.

-- Why not also give normalization proof to substType in similar fashion?
-- → Because such a proof would also need to be supplied by `normalizeType` and a lemma to produce such a proof from a kinding proof in the context of a recursive application of `normalizeType` would already implement `normalizeKinding` and in particular would have to mention `normalizeType` in the signature.
-- Could this still work?
--------------------------------------------------------------------------------


-- normalizeWellKindedType : (τ : Type) → Δ ⊢ τ ∶ κ → Typeₙ
-- normalizeWellKindedType (var x)     (var {κ = κ} p) = η-expandTypeᵤ κ (⟨ x ⟩ [])
-- normalizeWellKindedType (fun τ₁ τ₂) (fun p₁ p₂)     = fun (normalizeWellKindedType τ₁ p₁) (normalizeWellKindedType τ₂ p₂)
-- normalizeWellKindedType (app τ₁ τ₂) (app {κ = κ} {κ' = κ'} p₁ p₂) with normalizeWellKindedType τ₁ p₁
-- ... | lam κ τ = substTypeₙ τ zero κ (normalizeWellKindedType τ₂ p₂)
-- ... | fun _ _ = stuck
-- ... | all _ _ = stuck
-- ... | neu _   = stuck
-- ... | stuck   = stuck
-- normalizeWellKindedType (lam κ τ) (lam p) = lam κ (normalizeWellKindedType τ p)
-- normalizeWellKindedType (all κ τ) (all p) = all κ (normalizeWellKindedType τ p)

normalizeWellKindedType : (τ : Type) → Δ ⊢ τ ∶ κ → Typeₙ
normalizeWellKindedType (var x)     (var {κ = κ} p) = η-expandTypeᵤ κ (⟨ x ⟩ [])
normalizeWellKindedType (fun τ₁ τ₂) (fun p₁ p₂)     = fun (normalizeWellKindedType τ₁ p₁) (normalizeWellKindedType τ₂ p₂)
normalizeWellKindedType (app τ₁ τ₂) (app p₁ p₂)     = applyTypeₙ (normalizeWellKindedType τ₁ p₁) (normalizeWellKindedType τ₂ p₂)
normalizeWellKindedType (lam κ τ)   (lam p)         = lam κ (normalizeWellKindedType τ p)
normalizeWellKindedType (all κ τ)   (all p)         = all κ (normalizeWellKindedType τ p)


--------------------------------------------------------------------------------

-- lemma-normalizedWellKindedTypesRemainWellKinded : (p : Δ ⊢ τ ∶ κ) → Δ ⊢ₙ normalizeWellKindedType τ p ∶ κ
-- lemma-normalizedWellKindedTypesRemainWellKinded (var x)     = {! τ  !}
-- lemma-normalizedWellKindedTypesRemainWellKinded (fun p₁ p₂) = fun (lemma-normalizedWellKindedTypesRemainWellKinded p₁) (lemma-normalizedWellKindedTypesRemainWellKinded p₂)
-- lemma-normalizedWellKindedTypesRemainWellKinded (all p)     = all (lemma-normalizedWellKindedTypesRemainWellKinded p)
-- lemma-normalizedWellKindedTypesRemainWellKinded (lam p)     = lam (lemma-normalizedWellKindedTypesRemainWellKinded p)
-- lemma-normalizedWellKindedTypesRemainWellKinded (app {τ₁ = τ₁} {τ₂ = τ₂} p₁ p₂)
--   with normalizeWellKindedType τ₁ p₁ | normalizeWellKindedType τ₂ p₂ | lemma-normalizedWellKindedTypesRemainWellKinded p₁ | lemma-normalizedWellKindedTypesRemainWellKinded p₂
-- ... | τ₁ₙ | τ₂ₙ | lam p | pₛ
--   = {!   !}

-- lemma-typeFunctionsNormalizeToLam : (p : Δ ⊢ τ ∶ κ ⇒ κ') → ∃[ τₙ ] normalizeWellKindedType τ p ≡ lam κ τₙ × Δ ⊢ₙ τₙ ∶ κ'
-- lemma-typeFunctionsNormalizeToLam {κ = κ} {κ' = κ'} (var {x = x} p) = ⟨ normalizeTypeAtᵤ κ' (⟨ suc x ⟩ (normalizeTypeAtᵤ κ (⟨ zero ⟩ []) ∷ [])) , ⟨ refl , {!   !} ⟩ ⟩
-- lemma-typeFunctionsNormalizeToLam (lam {τ = τ} p) = ⟨ normalizeWellKindedType τ p , ⟨ refl , {!   !} ⟩ ⟩
-- lemma-typeFunctionsNormalizeToLam (app {τ₁ = τ₁} {κ = kₛ} {κ' = κ ⇒ κ'} {τ₂ = τ₂} p₁ p₂)
--   with ⟨ τ₁ₙ' , ⟨ eq , lam {τₙ = τ₁ₙ'' } pₙ'' ⟩ ⟩ ← lemma-typeFunctionsNormalizeToLam p₁
--   rewrite eq
--   = ⟨ substTypeₙ τ₁ₙ'' (suc zero) kₛ (weakenTypeAtₙ zero (normalizeWellKindedType τ₂ p₂)) .proj₁ , ⟨ refl , {!   !} ⟩ ⟩

-- lemma-typeFunctionsNormalizeToLam : (p : Δ ⊢ τ ∶ κ ⇒ κ') → ∃[ τₙ ] normalizeWellKindedType τ p ≡ lam κ τₙ
-- lemma-typeFunctionsNormalizeToLam {κ = κ} {κ' = κ'} (var {x = x} p) = ⟨ η-expandTypeᵤ κ' (⟨ suc x ⟩ (η-expandTypeᵤ κ (⟨ zero ⟩ []) ∷ [])) , refl ⟩
-- lemma-typeFunctionsNormalizeToLam (lam {τ = τ} p) = ⟨ normalizeWellKindedType τ p , refl ⟩
-- lemma-typeFunctionsNormalizeToLam (app {τ₁ = τ₁} {κ = κₛ} {κ' = κ ⇒ κ'} {τ₂ = τ₂} p₁ p₂)
--   with ⟨ τ₁ₙ' , eq ⟩ ← lemma-typeFunctionsNormalizeToLam p₁
--   rewrite eq
--   = {! ⟨ substTypeₙ τ₁ₙ'' (suc zero) kₛ (weakenTypeAtₙ zero (normalizeWellKindedType τ₂ p₂)) .proj₁ , {!   !} ⟩ !}

-- normalizeKinding' : (p : Δ ⊢ τ ∶ κ) → Δ ⊢ₙ normalizeWellKindedType τ p ∶ κ
-- normalizeKinding' (var p) = η-expandKindingᵤ (⟨ p ⟩ [])
-- normalizeKinding' (app {τ₁ = τ₁} p₁ p₂) with pₙ ← normalizeKinding' p₁
--   rewrite lemma-typeFunctionsNormalizeToLam p₁ .proj₂
--   with lam pₙ' ← pₙ = substKindingₙ pₙ' here (normalizeKinding' p₂)
-- normalizeKinding' (fun p₁ p₂) = fun (normalizeKinding' p₁) (normalizeKinding' p₂)
-- normalizeKinding' (lam p)     = lam (normalizeKinding' p)
-- normalizeKinding' (all p)     = all (normalizeKinding' p)

normalizeKinding' : (p : Δ ⊢ τ ∶ κ) → Δ ⊢ₙ normalizeWellKindedType τ p ∶ κ
normalizeKinding' (var p)     = η-expandKindingᵤ (⟨ p ⟩ [])
normalizeKinding' (app p₁ p₂) = applyKindingₙ (normalizeKinding' p₁) (normalizeKinding' p₂)
normalizeKinding' (fun p₁ p₂) = fun (normalizeKinding' p₁) (normalizeKinding' p₂)
normalizeKinding' (lam p)     = lam (normalizeKinding' p)
normalizeKinding' (all p)     = all (normalizeKinding' p)


--------------------------------------------------------------------------------

-- mutual
--   lemma-substTypePreservesKind : ∀ {τ τₛ} → Δ ⊢ₛ τ ∶ κ → Δ ∋ xₛ ↦ κₛ → Δ \\ xₛ ⊢ₛ τₛ ∶ κₛ → Δ \\ xₛ ⊢ₛ substTypeₛ τ xₛ κₛ τₛ ∶ κ
--   lemma-substTypePreservesKind {xₛ = xₛ} (⟨ var {x = x} pₓ ⟩ ps) pₓₛ pₛ with x ≟ xₛ
--   ... | no ref with ⟨ x' , refl ⟩ ← lemma-existsWeakenedIndex ref
--     = ⟨ var (strengthenIndexingAt xₛ pₓ) ⟩ lemma-substSpinePreservesKind ps pₓₛ pₛ
--   ... | yes refl with refl ← lookupUniqueness pₓ pₓₛ
--     = lemma-applyToSpinePreservesKind pₛ (lemma-substSpinePreservesKind ps pₓₛ pₛ)
--   lemma-substTypePreservesKind (⟨ fun p₁ p₂ ⟩ ps) pₓₛ pₛ = ⟨ fun (lemma-substTypePreservesKind p₁ pₓₛ pₛ) (lemma-substTypePreservesKind p₂ pₓₛ pₛ) ⟩ lemma-substSpinePreservesKind ps pₓₛ pₛ
--   lemma-substTypePreservesKind (⟨ all p ⟩ ps)     pₓₛ pₛ = ⟨ all (lemma-substTypePreservesKind p (weakenIndexingAt zero pₓₛ) (weakenKindingAtₛ zero pₛ)) ⟩ lemma-substSpinePreservesKind ps pₓₛ pₛ
--   lemma-substTypePreservesKind (⟨ lam p ⟩ ps)     pₓₛ pₛ = ⟨ lam (lemma-substTypePreservesKind p (weakenIndexingAt zero pₓₛ) (weakenKindingAtₛ zero pₛ)) ⟩ lemma-substSpinePreservesKind ps pₓₛ pₛ

--   lemma-substSpinePreservesKind : ∀ {τs τₛ} → Δ ∣ κ ⊢ₛ τs ∶ κ' → Δ ∋ xₛ ↦ κₛ → Δ \\ xₛ ⊢ₛ τₛ ∶ κₛ → Δ \\ xₛ ∣ κ ⊢ₛ substSpine τs xₛ κₛ τₛ ∶ κ'
--   lemma-substSpinePreservesKind []       _   _  = []
--   lemma-substSpinePreservesKind (p ∷ ps) pₓₛ pₛ = lemma-substTypePreservesKind p pₓₛ pₛ ∷ lemma-substSpinePreservesKind ps pₓₛ pₛ

--   lemma-applyPreservesKind : ∀ {τ τₛ} → Δ ⊢ₛ τ ∶ κ ⇒ κ' → Δ ⊢ₛ τₛ ∶ κ → Δ ⊢ₛ apply (κ ⇒ κ') τ τₛ ∶ κ'
--   lemma-applyPreservesKind (⟨ var pₓ ⟩ ps)       pₛ = {!   !}
--   lemma-applyPreservesKind (⟨ lam p ⟩ [])        pₛ = lemma-substTypePreservesKind p here pₛ
--   lemma-applyPreservesKind (⟨ lam p ⟩ (p' ∷ ps)) pₛ = {!   !}

--   lemma-applyToSpinePreservesKind : ∀ {τ τs} → Δ ⊢ₛ τ ∶ κ → Δ ∣ κ ⊢ₛ τs ∶ κ' → Δ ⊢ₛ applyToSpine κ τ τs ∶ κ'
--   lemma-applyToSpinePreservesKind p []        = p
--   lemma-applyToSpinePreservesKind {κ = κ ⇒ κ'} p (pₛ ∷ ps) = lemma-applyToSpinePreservesKind (lemma-applyPreservesKind p pₛ) ps