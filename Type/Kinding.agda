module Type.Kinding where

open import Prelude
open import Type
open import Type.Context


infix 3 _⊢_∶_
data _⊢_∶_ (Δ : KindCtx) : Type → Kind → Set where
  var : Δ ∋ x ↦ κ → Δ ⊢ var x ∶ κ
  fun : Δ ⊢ τ₁ ∶ ⋆ → Δ ⊢ τ₂ ∶ ⋆ → Δ ⊢ fun τ₁ τ₂ ∶ ⋆
  all : κ ∷ Δ ⊢ τ ∶ ⋆ → Δ ⊢ all κ τ ∶ ⋆
  lam : κ ∷ Δ ⊢ τ ∶ κ' → Δ ⊢ lam κ τ ∶ κ ⇒ κ'
  app : Δ ⊢ τ₁ ∶ κ ⇒ κ' → Δ ⊢ τ₂ ∶ κ → Δ ⊢ app τ₁ τ₂ ∶ κ'


kindingUniqueness : Δ ⊢ τ ∶ κ → Δ ⊢ τ ∶ κ' → κ ≡ κ'
kindingUniqueness (var prf)    (var prf')    = lookupUniqueness prf prf'
kindingUniqueness (fun _ _)    (fun _ _)     = refl
kindingUniqueness (all _)      (all _)       = refl
kindingUniqueness (lam prf)    (lam prf')    = cong (λ κ' → _ ⇒ κ') (kindingUniqueness prf prf')
kindingUniqueness (app prf₁ _) (app prf₁' _) = ⇒-inj (kindingUniqueness prf₁ prf₁') .proj₂

mutual
  inferKind : ∀ (Δ : KindCtx) (τ : Type) → Dec (∃[ κ ] Δ ⊢ τ ∶ κ)
  inferKind Δ (var x) with find Δ x
  ... | no ref          = no λ { ⟨ κ , var prf ⟩ → ref ⟨ κ , prf ⟩ }
  ... | yes ⟨ κ , prf ⟩ = yes ⟨ κ , var prf ⟩
  inferKind Δ (fun τ₁ τ₂) with checkKind Δ ⋆ τ₁
  ... | no ref = no λ { ⟨ ⋆ , fun prf₁ _ ⟩ → ref prf₁ }
  ... | yes prf₁ with checkKind Δ ⋆ τ₂
  ...   | no ref   = no λ { ⟨ ⋆ , fun _ prf₂ ⟩ → ref prf₂ }
  ...   | yes prf₂ = yes ⟨ ⋆ , fun prf₁ prf₂ ⟩
  inferKind Δ (lam κ τ) with inferKind (κ ∷ Δ) τ
  ... | no ref           = no λ { ⟨ κ ⇒ κ' , lam prf ⟩ → ref ⟨ κ' , prf ⟩ }
  ... | yes ⟨ κ' , prf ⟩ = yes ⟨ κ ⇒ κ' , lam prf ⟩
  inferKind Δ (app τ₁ τ₂) with inferKind Δ τ₁
  ... | no ref           = no λ { ⟨ κ' , app prf₁ _ ⟩ → ref ⟨ _ ⇒ κ' , prf₁ ⟩ }
  ... | yes ⟨ ⋆ , prf₁ ⟩ = no λ { ⟨ κ , app prf₁' _ ⟩ → case (kindingUniqueness prf₁ prf₁') of λ () }
  ... | yes ⟨ κ ⇒ κ' , prf₁ ⟩ with checkKind Δ κ τ₂
  ...   | no ref   = no λ { ⟨ κ , app prf₁' prf₂ ⟩ → case ⇒-inj (kindingUniqueness prf₁ prf₁') .proj₁ of λ { refl → ref prf₂ } }
  ...   | yes prf₂ = yes ⟨ κ' , app prf₁ prf₂ ⟩
  inferKind Δ (all κ τ) with checkKind (κ ∷ Δ) ⋆ τ
  ... | no ref = no λ { ⟨ ⋆ , all prf ⟩ → ref prf }
  ... | yes prf = yes ⟨ ⋆ , all prf ⟩

  checkKind : ∀ (Δ : KindCtx) (κ : Kind) (τ : Type) → Dec (Δ ⊢ τ ∶ κ)
  checkKind Δ κ τ with inferKind Δ τ
  ... | no ref = no λ prf → ref ⟨ κ , prf ⟩
  ... | yes ⟨ κ' , prf ⟩ with κ' ≟ₖ κ
  ...   | no ref   = no λ prf' → ref (kindingUniqueness prf prf')
  ...   | yes refl = yes prf