module Term.Typing where

open import Prelude
open import Term
open import Term.Context
open import Type.Kinding
open import Type.Substitution
open import Type.Equality
open import Type.Normalization


infix 3 _,_⊢_∶_
data _,_⊢_∶_ (Δ : KindCtx) (Γ : TypeCtx) : Term → Type → Set where
  var : ∀ {x τ}
    → Δ ⊢ₙ τ ∶ ⋆
    → Γ ∋ x ↦ τ
    → Δ , Γ ⊢ var x ∶ τ
  lam : ∀ {τ τ' t}
    → Δ ⊢ₙ fun τ τ' ∶ ⋆
    → Δ ⊢ₙ τ ∶ ⋆
    → Δ , (τ ∷ Γ) ⊢ t ∶ τ'
    → Δ , Γ ⊢ lam τ t ∶ fun τ τ'
  app : ∀ {τ τ' t t'}
    → Δ ⊢ₙ τ' ∶ ⋆
    → Δ , Γ ⊢ t ∶ fun τ τ'
    → Δ , Γ ⊢ t' ∶ τ
    → Δ , Γ ⊢ app t t' ∶ τ'
  tlam : ∀ {κ τ t}
    → Δ ⊢ₙ all κ τ ∶ ⋆
    → κ ∷ Δ , Γ ⊢ t ∶ τ
    → Δ , Γ ⊢ tlam κ t ∶ all κ τ
  tapp : ∀ {κ τ t τₛ}
    → Δ ⊢ₙ τ [ τₛ ] ∶ ⋆
    → Δ , Γ ⊢ t ∶ all κ τ
    → Δ ⊢ₙ τₛ ∶ κ
    → Δ , Γ ⊢ tapp t τₛ ∶ τ [ τₛ ]


extractKindingFromTyping : Δ , Γ ⊢ e ∶ τ → Δ ⊢ₙ τ ∶ ⋆
extractKindingFromTyping (var prfₙ _)    = prfₙ
extractKindingFromTyping (lam prfₙ _ _)  = prfₙ
extractKindingFromTyping (app prfₙ _ _)  = prfₙ
extractKindingFromTyping (tlam prfₙ _)   = prfₙ
extractKindingFromTyping (tapp prfₙ _ _) = prfₙ


typingUniqueness : Δ , Γ ⊢ t ∶ τ → Δ , Γ ⊢ t ∶ τ' → Δ ⊢ₙ τ ≡ₜ τ' ∶ ⋆
typingUniqueness (var prfₙ prf)         (var prfₙ' prf')          with refl     ← lookupUniqueness prf prf'    = refl prfₙ
typingUniqueness (lam prfₙ₁ prfₙ₂ prf)  (lam prfₙ₁' prfₙ₂' prf')  with (refl _) ← typingUniqueness prf prf'   = refl prfₙ₁
typingUniqueness (app prfₙ prf₁ prf₂)   (app prfₙ' prf₁' prf₂')   with (refl _) ← typingUniqueness prf₁ prf₁' = refl prfₙ
typingUniqueness (tlam prfₙ prf)        (tlam prfₙ' prf')         with (refl _) ← typingUniqueness prf prf'   = refl prfₙ
typingUniqueness (tapp prfₙ₁ prf prfₙ₂) (tapp prfₙ₁' prf' prfₙ₂') with (refl _) ← typingUniqueness prf prf'   = refl prfₙ₁

checkFun : Δ ⊢ₙ τ ∶ ⋆ → Dec (∃[ τ₁ ] ∃[ τ₂ ] Δ ⊢ₙ τ ≡ₜ fun τ₁ τ₂ ∶ ⋆)
checkFun (neu (var _))                       = no λ ()
checkFun (neu (app _ _))                     = no λ ()
checkFun (fun {τ₁ = τ₁} {τ₂ = τ₂} prf₁ prf₂) = yes ⟨ τ₁ , ⟨ τ₂ , refl (fun prf₁ prf₂) ⟩ ⟩
checkFun (all _)                             = no λ ()


checkAll : Δ ⊢ₙ τ ∶ ⋆ → Dec (∃[ κ ] ∃[ τ' ] Δ ⊢ₙ τ ≡ₜ all κ τ' ∶ ⋆)
checkAll (neu (var _))   = no λ ()
checkAll (neu (app _ _)) = no λ ()
checkAll (fun  _ _)      = no λ ()
checkAll (all {κ = κ} {τ = τ'} prf) = yes ⟨ κ , ⟨ τ' , refl (all prf) ⟩ ⟩


checkTypeEqualityₙ : Δ ⊢ₙ τ ∶ κ → Δ ⊢ₙ τ' ∶ κ → Dec (Δ ⊢ₙ τ ≡ₜ τ' ∶ κ)
checkTypeEqualityₙ {τ = τ} {τ' = τ'} prfₙ prfₙ' with τ ≟ₜ τ'
... | yes eq rewrite eq = yes (refl prfₙ)
... | no  ref           = no λ { (refl _) → ref refl }


checkKindₙ : ∀ (Δ : KindCtx) (κ : Kind) (τ : Type) → Dec (Δ ⊢ₙ τ ∶ κ)
checkKindₙ Δ κ τ with checkKind Δ κ τ
... | no ref = no λ { prf → ref (denormalizeKinding prf) }
... | yes prf with prfₙ ← normalizeKinding prf with τ ≟ₜ (prfₙ .normalForm)
...   | no ref   = no λ prfₙ' → let prfₙ' = record { normalForm = τ ; normalization = prfₙ' ; soundness = trefl prf }
                                in case normalizationUniqueness prfₙ prfₙ' of λ { (refl _) → ref refl }
...   | yes refl = yes (prfₙ .normalization)


mutual
  inferType : ∀ (Δ : KindCtx) (Γ : TypeCtx) (e : Term) → Dec (∃[ τ ] Δ , Γ ⊢ e ∶ τ)
  inferType Δ Γ (var x) with find Γ x
  ... | no ref = no λ { ⟨ τ , var _ prf ⟩ → ref ⟨ τ , prf ⟩ }
  ... | yes ⟨ τ , prf ⟩ with checkKindₙ Δ ⋆ τ
  ...   | no ref = no λ { ⟨ τ' , var prfₖ prf' ⟩ → case lookupUniqueness prf prf' of λ { refl → ref prfₖ } }
  ...   | yes prfₖ = yes ⟨ τ , var prfₖ prf ⟩
  inferType Δ Γ (lam τ e) with checkKindₙ Δ ⋆ τ
  ... | no ref = no λ { ⟨ fun τ τ' , lam _ prf₁ _ ⟩ → ref prf₁ }
  ... | yes prfₖ₁ with inferType Δ (τ ∷ Γ) e
  ...   | no ref = no λ { ⟨ fun τ τ' , lam _ _ prf₂ ⟩ → ref ⟨ τ' , prf₂ ⟩ }
  ...   | yes ⟨ τ' , prf₂ ⟩ with checkKindₙ Δ ⋆ τ'
  ...     | no ref = no λ { ⟨ fun τ τ' , lam (fun _ prfₖ₂) _ prf₂' ⟩ → case typingUniqueness prf₂ prf₂' of λ { (refl _) → ref prfₖ₂ } }
  ...     | yes prfₖ₂ = yes ⟨ fun τ τ' , lam (fun prfₖ₁ prfₖ₂) prfₖ₁ prf₂ ⟩
  inferType Δ Γ (app e₁ e₂) with inferType Δ Γ e₁
  ... | no ref = no λ { ⟨ τ' , app _ prf₁ _ ⟩ → ref ⟨ fun _ τ' , prf₁ ⟩ }
  ... | yes ⟨ τ , prf₁ ⟩ with τ | prf₁ | checkFun (extractKindingFromTyping prf₁)
  ...   | _         | prf₁ | no ref = no λ { ⟨ τ' , app _ prf₁' _ ⟩ → case (typingUniqueness prf₁ prf₁') of λ { eq → ref ⟨ _ , ⟨ _ , eq ⟩ ⟩ } }
  ...   | fun τ₁ τ₂ | prf₁ | yes ⟨ _ , ⟨ _ , refl _ ⟩ ⟩ with checkType Δ Γ τ₁ e₂
  ...     | no ref = no λ { ⟨ τ , app _ prf₁' prf₂ ⟩ → case typingUniqueness prf₁ prf₁' of λ { (refl _) → ref prf₂ } }
  ...     | yes prf₂ with checkKindₙ Δ ⋆ τ₂
  ...       | no ref = no λ { ⟨ τ , app prfₖ prf₁' _ ⟩ → case typingUniqueness prf₁ prf₁' of λ { (refl _) → ref prfₖ } }
  ...       | yes prfₖ = yes ⟨ τ₂ , app prfₖ prf₁ prf₂ ⟩
  inferType Δ Γ (tlam κ e) with inferType (κ ∷ Δ) Γ e
  ... | no ref = no λ { ⟨ all κ τ , tlam _ prf ⟩ → ref ⟨ τ , prf ⟩ }
  ... | yes ⟨ τ , prf ⟩ with checkKindₙ (κ ∷ Δ) ⋆ τ
  ...   | no ref = no λ { ⟨ all κ τ , tlam (all prfₖ) prf' ⟩ → case typingUniqueness prf prf' of λ { (refl _) → ref prfₖ } }
  ...   | yes prfₖ = yes ⟨ all κ τ , tlam (all prfₖ) prf ⟩
  inferType Δ Γ (tapp e τₛ) with inferType Δ Γ e
  ... | no ref = no λ { ⟨ τ , tapp _ prf prfₖ ⟩ → ref ⟨ all _ _ , prf ⟩ }
  ... | yes ⟨ τ , prf ⟩ with τ | prf | checkAll (extractKindingFromTyping prf)
  ...   | _       | prf | no ref = no λ { ⟨ τ , tapp _ prf' _ ⟩ → case typingUniqueness prf prf' of λ eq → ref ⟨ _ , ⟨ _ , eq ⟩ ⟩ }
  ...   | all κ τ | prf | yes ⟨ _ , ⟨ _ , refl _ ⟩ ⟩ with checkKindₙ Δ κ τₛ
  ...     | no ref = no λ { ⟨ τ , tapp _ prf' prfₖ ⟩ → case typingUniqueness prf prf' of λ { (refl _) → ref prfₖ } }
  ...     | yes prfₖₛ with checkKindₙ Δ ⋆ (τ [ τₛ ])
  ...       | no ref = no λ { ⟨ _ , tapp prfₖ prf' prfₖₛ' ⟩ → (case typingUniqueness prf prf' of λ { (refl _) → ref prfₖ }) }
  ...       | yes prfₖ = yes ⟨ τ [ τₛ ] , tapp prfₖ prf prfₖₛ ⟩

  checkType : ∀ (Δ : KindCtx) (Γ : TypeCtx) (τ : Type) (e : Term) → Dec (Δ , Γ ⊢ e ∶ τ)
  checkType Δ Γ τ e with checkKindₙ Δ ⋆ τ
  ... | no ref = no λ prf → ref (extractKindingFromTyping prf)
  ... | yes prfₖ with inferType Δ Γ e
  ...   | no ref = no λ prf → ref ⟨ τ , prf ⟩
  ...   | yes ⟨ τ' , prf ⟩ with checkTypeEqualityₙ (extractKindingFromTyping prf) prfₖ
  ...     | no ref   = no λ prf' → ref (typingUniqueness prf prf')
  ...     | yes (refl _) = yes prf