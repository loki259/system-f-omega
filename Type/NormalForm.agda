module Type.NormalForm where

open import Prelude

open import Kind public


mutual
  data Typeₙ : Set where
    neu   : Typeᵤ → Typeₙ
    fun   : Typeₙ → Typeₙ → Typeₙ
    lam   : Kind → Typeₙ → Typeₙ
    all   : Kind → Typeₙ → Typeₙ
    stuck : Typeₙ

  data Typeᵤ : Set where
    ⟨_⟩_ : Index → Spineₙ → Typeᵤ

  Spineₙ : Set
  Spineₙ = List Typeₙ

variable
  τₙ τₙ' τₙ₁ τₙ₁' τₙ₂ τₙ₂' τₙ₃ τₙ₃' τₙₛ : Typeₙ
  τᵤ τᵤ' τᵤ₁ τᵤ₁' τᵤ₂ τᵤ₂' τᵤ₃ τᵤ₃' τᵤₛ : Typeᵤ
  τs τs' τsₙ τsₙ' τs₁ τs₁' τs₂ τs₂' τs₃ τs₃' : Spineₙ


appendToSpineₙ : Spineₙ → Typeₙ → Spineₙ
appendToSpineₙ []        τₙ' = τₙ' ∷ []
appendToSpineₙ (τₙ ∷ τs) τₙ' = τₙ ∷ appendToSpineₙ τs τₙ'