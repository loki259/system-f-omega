module Type.SpineForm where

open import Prelude

open import Kind public


mutual
  data Typeₛ : Set where
    ⟨_⟩_ : Typeₕ → Spine → Typeₛ
    -- app : Typeₕ → Spine → Typeₛ
  
  data Typeₕ : Set where
    var : Index → Typeₕ
    fun : Typeₛ → Typeₛ → Typeₕ
    lam : Kind → Typeₛ → Typeₕ
    all : Kind → Typeₛ → Typeₕ
  
  Spine : Set
  Spine = List Typeₛ

-- pattern ⟨_⟩_ = app
-- pattern app = ⟨_⟩_

variable
  -- π π' π₁ π₁' π₂ π₂' π₃ π₃' πₛ : Typeₛ
  τₛ τₛ' τₛ₁ τₛ₁' τₛ₂ τₛ₂' τₛ₃ τₛ₃' : Typeₛ
  τₕ τₕ' : Typeₕ
  -- πs πs' πs₁ πs₁' πs₂ πs₂' πs₃ πs₃' : Spine
  τs τs' τsₛ τsₛ' τs₁ τs₁' τs₂ τs₂' τs₃ τs₃' : Spine


appendToSpine : Spine → Typeₛ → Spine
appendToSpine = _∷ʳ_

concatSpines : Spine → Spine → Spine
concatSpines = _++_