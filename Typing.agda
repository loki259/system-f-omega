open import Prelude
open import Syntax
open import Kinding


module Typing where

TypeCtx : Set
TypeCtx = Ctx Type

variable
  Γ : TypeCtx

postulate
  weaken : TypeCtx → TypeCtx
  --                    τ        α.t            t[τ/α]
  instantiate : Type → Type → Type


-- infix 3 _≡ₜ_
-- data _≡ₜ_ {m} : Type m → Type m → Set where
--   refl  : ∀ {τ} → τ ≡ₜ τ
--   sym   : ∀ {τ τ'} → τ ≡ₜ τ' → τ' ≡ₜ τ
--   trans : ∀ {τ₁ τ₂ τ₃} → τ₁ ≡ₜ τ₂ → τ₂ ≡ₜ τ₃ → τ₁ ≡ₜ τ₃
--   fun   : ∀ {τ₁ τ₁' τ₂ τ₂'} → τ₁ ≡ₜ τ₁' → τ₂ ≡ₜ τ₂' → fun τ₁ τ₂ ≡ₜ fun τ₁' τ₂'
--   all   : ∀ {κ τ τ'} → τ ≡ₜ τ' → all κ τ ≡ₜ all κ τ'
--   lam   : ∀ {κ τ τ'} → τ ≡ₜ τ' → lam κ τ ≡ₜ lam κ τ'
--   app   : ∀ {τ₁ τ₁' τ₂ τ₂'} → τ₁ ≡ₜ τ₁' → τ₂ ≡ₜ τ₂' → app τ₁ τ₂ ≡ₜ app τ₁' τ₂'
--   beta  : ∀ {κ τ τ'} → app (lam κ τ) τ' ≡ₜ instantiate τ' τ

infix 3 _,_⊢_∶_
data _,_⊢_∶_ (Δ : KindCtx) (Γ : TypeCtx) : Term → Type → Set where
  var : ∀ {v}
    → Δ , Γ ⊢ var v ∶ {!   !} -- lookup Γ v
  lam : ∀ {τ τ' t}
    → Δ , (τ ∷ Γ) ⊢ t ∶ τ'
    → Δ ⊢ τ ∶ ⋆
    → Δ , Γ ⊢ lam τ t ∶ fun τ τ'
  app : ∀ {τ τ' t t'}
    → Δ , Γ ⊢ t ∶ fun τ τ'
    → Δ , Γ ⊢ t' ∶ τ
    → Δ , Γ ⊢ app t t' ∶ τ'
  tlam : ∀ {κ τ t}
    → κ ∷ Δ , weaken Γ ⊢ t ∶ τ
    → Δ , Γ ⊢ tlam κ t ∶ all κ τ
  tapp : ∀ {κ τ t τ'}
    → Δ , Γ ⊢ t ∶ all κ τ
    → Δ ⊢ τ' ∶ κ
    → Δ , Γ ⊢ tapp t τ' ∶ instantiate τ' τ
  -- type-eq : ∀ {t τ τ'}
  --   → Δ , Γ ⊢ t ∶ τ
  --   → τ ≡ₜ τ'
  --   → Δ , Γ ⊢ t ∶ τ'


_≟ₜ_ : DecidableEquality Type
τ₁ ≟ₜ τ₂ = ?