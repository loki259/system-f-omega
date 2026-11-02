module Type.SpineForm.Kinding where

open import Prelude
open import Type.SpineForm
open import Type.Context


mutual
  infix 3 _⊢ₛ_∶_
  data _⊢ₛ_∶_ (Δ : KindCtx) : Typeₛ → Kind → Set where
    ⟨_⟩_ : Δ ⊢ₕ τₕ ∶ κ → Δ ∣ κ ⊢ₛ τs ∶ κ' → Δ ⊢ₛ ⟨ τₕ ⟩ τs ∶ κ'

  infix 3 _⊢ₕ_∶_
  data _⊢ₕ_∶_ (Δ : KindCtx) : Typeₕ → Kind → Set where
    var : Δ ∋ x ↦ κ → Δ ⊢ₕ var x ∶ κ
    fun : Δ ⊢ₛ τₛ₁ ∶ ⋆ → Δ ⊢ₛ τₛ₂ ∶ ⋆ → Δ ⊢ₕ fun τₛ₁ τₛ₂ ∶ ⋆
    all : κ ∷ Δ ⊢ₛ τₛ ∶ ⋆ → Δ ⊢ₕ all κ τₛ ∶ ⋆
    lam : κ ∷ Δ ⊢ₛ τₛ ∶ κ' → Δ ⊢ₕ lam κ τₛ ∶ κ ⇒ κ'
  
  infix 3 _∣_⊢ₛ_∶_
  data _∣_⊢ₛ_∶_ (Δ : KindCtx) : Kind → Spine → Kind → Set where
    []  : Δ ∣ κ ⊢ₛ [] ∶ κ
    _∷_ : Δ ⊢ₛ τₛ ∶ κ → Δ ∣ κ' ⊢ₛ τs ∶ κ'' → Δ ∣ κ ⇒ κ' ⊢ₛ τₛ ∷ τs ∶ κ''


appendToKindingSpine : Δ ∣ κ ⊢ₛ τs ∶ κ' ⇒ κ'' → Δ ⊢ₛ τₛ ∶ κ' → Δ ∣ κ ⊢ₛ appendToSpine τs τₛ ∶ κ''
appendToKindingSpine []       p' = p' ∷ []
appendToKindingSpine (p ∷ ps) p' = p ∷ appendToKindingSpine ps p'

concatKindingSpines : Δ ∣ κ ⊢ₛ τs ∶ κ' → Δ ∣ κ' ⊢ₛ τs' ∶ κ'' → Δ ∣ κ ⊢ₛ concatSpines τs τs' ∶ κ''
concatKindingSpines []       ps' = ps'
concatKindingSpines (p ∷ ps) ps' = p ∷ concatKindingSpines ps ps'


lemma-varIndexExistsInCtx : Δ ⊢ₕ var x ∶ κ → ∃[ p ] find Δ x ≡ yes ⟨ κ , p ⟩
lemma-varIndexExistsInCtx {Δ = Δ} {x = x} {κ = κ} (var p) with find Δ x
... | no ref         with () ← ref ⟨ κ , p ⟩
... | yes ⟨ _ , p' ⟩ with refl ← lookupUniqueness p p' = ⟨ p' , refl ⟩