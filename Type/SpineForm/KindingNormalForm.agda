module Type.SpineForm.KindingNormalForm where

open import Prelude
open import Type.Context
open import Type.SpineForm


mutual
  infix 3 _⊢ₙ_∶_
  data _⊢ₙ_∶_ (Δ : KindCtx) : Typeₛ → Kind → Set where
    neu : Δ ⊢ᵤ τₛ ∶ ⋆ → Δ ⊢ₙ τₛ ∶ ⋆
    fun : Δ ⊢ₙ τₛ₁ ∶ ⋆ → Δ ⊢ₙ τₛ₂ ∶ ⋆ → Δ ⊢ₙ ⟨ fun τₛ₁ τₛ₂ ⟩ [] ∶ ⋆
    all : κ ∷ Δ ⊢ₙ τₛ ∶ ⋆ → Δ ⊢ₙ ⟨ all κ τₛ ⟩ [] ∶ ⋆
    lam : κ ∷ Δ ⊢ₙ τₛ ∶ κ' → Δ ⊢ₙ ⟨ lam κ τₛ ⟩ [] ∶ κ ⇒ κ'

  infix 3 _⊢ᵤ_∶_
  data _⊢ᵤ_∶_ (Δ : KindCtx) : Typeₛ → Kind → Set where
    ⟨_⟩_ : Δ ∋ x ↦ κ → Δ ∣ κ ⊢ₙ τs ∶ κ' → Δ ⊢ᵤ ⟨ var x ⟩ τs ∶ κ'
  
  infix 3 _∣_⊢ₙ_∶_
  data _∣_⊢ₙ_∶_ (Δ : KindCtx) : Kind → Spine → Kind → Set where
    []  : Δ ∣ κ ⊢ₙ [] ∶ κ
    _∷_ : Δ ⊢ₙ τₛ ∶ κ → Δ ∣ κ' ⊢ₙ τs ∶ κ'' → Δ ∣ κ ⇒ κ' ⊢ₙ τₛ ∷ τs ∶ κ''


appendToKindingSpineₙ : Δ ∣ κ ⊢ₙ τs ∶ κ' ⇒ κ'' → Δ ⊢ₙ τₛ ∶ κ' → Δ ∣ κ ⊢ₙ appendToSpine τs τₛ ∶ κ''
appendToKindingSpineₙ []       p' = p' ∷ []
appendToKindingSpineₙ (p ∷ ps) p' = p ∷ appendToKindingSpineₙ ps p'

concatKindingSpinesₙ : Δ ∣ κ ⊢ₙ τs ∶ κ' → Δ ∣ κ' ⊢ₙ τs' ∶ κ'' → Δ ∣ κ ⊢ₙ concatSpines τs τs' ∶ κ''
concatKindingSpinesₙ []       ps' = ps'
concatKindingSpinesₙ (p ∷ ps) ps' = p ∷ concatKindingSpinesₙ ps ps'