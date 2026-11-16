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


mutual
  lemma-weakenTypeAtₙ-commutativity : Δ ⊢ₙ τₙ ∶ κ → xᵣ ≤ xᵣ' → weakenTypeAtₙ xᵣ (weakenTypeAtₙ xᵣ' τₙ) ≡ weakenTypeAtₙ (suc xᵣ') (weakenTypeAtₙ xᵣ τₙ)
  lemma-weakenTypeAtₙ-commutativity (neu pᵤ)        ≤-p = cong neu (lemma-weakenTypeAtᵤ-commutativity pᵤ ≤-p)
  lemma-weakenTypeAtₙ-commutativity (fun p₁ p₂)     ≤-p = cong₂ fun (lemma-weakenTypeAtₙ-commutativity p₁ ≤-p) (lemma-weakenTypeAtₙ-commutativity p₂ ≤-p)
  lemma-weakenTypeAtₙ-commutativity (all {κ = κ} p) ≤-p = cong (all κ) (lemma-weakenTypeAtₙ-commutativity p (s≤s ≤-p))
  lemma-weakenTypeAtₙ-commutativity (lam {κ = κ} p) ≤-p = cong (lam κ) (lemma-weakenTypeAtₙ-commutativity p (s≤s ≤-p))

  lemma-weakenTypeAtᵤ-commutativity : Δ ⊢ᵤ τᵤ ∶ κ → xᵣ ≤ xᵣ' → weakenTypeAtᵤ xᵣ (weakenTypeAtᵤ xᵣ' τᵤ) ≡ weakenTypeAtᵤ (suc xᵣ') (weakenTypeAtᵤ xᵣ τᵤ)
  lemma-weakenTypeAtᵤ-commutativity (⟨ pₓ ⟩ ps) ≤-p = cong₂ ⟨_⟩_ (lemma-weakenIndexAt-commutativity pₓ ≤-p) (lemma-weakenSpineAtₙ-commutativity ps ≤-p)

  lemma-weakenSpineAtₙ-commutativity : Δ ∣ κ ⊢ₙ τs ∶ κ' → xᵣ ≤ xᵣ' → weakenSpineAtₙ xᵣ (weakenSpineAtₙ xᵣ' τs) ≡ weakenSpineAtₙ (suc xᵣ') (weakenSpineAtₙ xᵣ τs)
  lemma-weakenSpineAtₙ-commutativity []       ≤-p = refl
  lemma-weakenSpineAtₙ-commutativity (p ∷ ps) ≤-p = cong₂ _∷_ (lemma-weakenTypeAtₙ-commutativity p ≤-p) (lemma-weakenSpineAtₙ-commutativity ps ≤-p)


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