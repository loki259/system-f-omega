module Type.NormalForm.Kinding where

open import Prelude
open import Type.NormalForm
open import Type.Context


mutual
  infix 3 _⊢ₙ_∶_
  data _⊢ₙ_∶_ (Δ : KindCtx) : Typeₙ → Kind → Set where
    neu : Δ ⊢ᵤ τᵤ ∶ ⋆ → Δ ⊢ₙ neu τᵤ ∶ ⋆
    fun : Δ ⊢ₙ τₙ₁ ∶ ⋆ → Δ ⊢ₙ τₙ₂ ∶ ⋆ → Δ ⊢ₙ fun τₙ₁ τₙ₂ ∶ ⋆
    all : κ ∷ Δ ⊢ₙ τₙ ∶ ⋆ → Δ ⊢ₙ all κ τₙ ∶ ⋆
    lam : κ ∷ Δ ⊢ₙ τₙ ∶ κ' → Δ ⊢ₙ lam κ τₙ ∶ κ ⇒ κ'

  infix 3 _⊢ᵤ_∶_
  data _⊢ᵤ_∶_ (Δ : KindCtx) : Typeᵤ → Kind → Set where
    ⟨_⟩_ : Δ ∋ x ↦ κ → Δ ∣ κ ⊢ₙ τs ∶ κ' → Δ ⊢ᵤ ⟨ x ⟩ τs ∶ κ'
  
  infix 3 _∣_⊢ₙ_∶_
  data _∣_⊢ₙ_∶_ (Δ : KindCtx) : Kind → Spineₙ → Kind → Set where
    []  : Δ ∣ κ ⊢ₙ [] ∶ κ
    _∷_ : Δ ⊢ₙ τₙ ∶ κ → Δ ∣ κ' ⊢ₙ τs ∶ κ'' → Δ ∣ κ ⇒ κ' ⊢ₙ τₙ ∷ τs ∶ κ''


appendToKindingSpineₙ : Δ ∣ κ ⊢ₙ τs ∶ κ' ⇒ κ'' → Δ ⊢ₙ τₙ ∶ κ' → Δ ∣ κ ⊢ₙ appendToSpineₙ τs τₙ ∶ κ''
appendToKindingSpineₙ []       p' = p' ∷ []
appendToKindingSpineₙ (p ∷ ps) p' = p ∷ appendToKindingSpineₙ ps p'