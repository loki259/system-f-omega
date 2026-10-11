module Term.Typing.Inference where

open import Prelude
open import Term.Typing
open import Type.Typing.Normalization


-- dom≡ₜ : ∀ {Δ τ₁ τ₁' τ₂ τ₂'} → Δ ⊢ fun τ₁ τ₂ ≡ₜ fun τ₁' τ₂' ∶ ⋆ → Δ ⊢ τ₁ ≡ₜ τ₁' ∶ ⋆
-- dom≡ₜ = {!!}
-- --dom≡ₜ trefl = trefl
-- --dom≡ₜ (tsym eq) = tsym (dom≡ₜ eq)
-- --dom≡ₜ (ttrans eq₁ eq₂) = {! !}
-- --dom≡ₜ (fun eq₁ _) = eq₁

-- rng≡ₜ : ∀ {Δ τ₁ τ₁' τ₂ τ₂'} → Δ ⊢ fun τ₁ τ₂ ≡ₜ fun τ₁' τ₂' ∶ ⋆ → Δ ⊢ τ₂ ≡ₜ τ₂' ∶ ⋆
-- rng≡ₜ = {!!}
-- --rng≡ₜ trefl = trefl
-- --rng≡ₜ (tsym eq) = tsym (rng≡ₜ eq)
-- --rng≡ₜ (ttrans eq₁ eq₂) = {!   !}
-- --rng≡ₜ (fun _ eq₂) = eq₂

-- uniq-⊢ₜ : ∀ {Δ Γ t τ τ'} → Δ , Γ ⊢ t ∶ₙ τ → Δ , Γ ⊢ t ∶ₙ τ' → τ ≡ τ'
-- uniq-⊢ₜ = {!   !}

-- decFun : (Δ : KindCtx) → (τ : Type) → Dec (∃[ τ₁ ] ∃[ τ₂ ] Δ ⊢ τ ≡ₜ fun τ₁ τ₂ ∶ ⋆)
-- decFun Δ τ = {!   !}

-- decAll : (Δ : KindCtx) → (τ : Type) → Dec (∃[ κ ] ∃[ τ' ] Δ ⊢ τ ≡ₜ all κ τ' ∶ ⋆)
-- decAll Δ τ = {!   !}

-- postulate
--   checkKindₙ : ∀ (Δ : KindCtx) (κ : Kind) (τₙ : Typeₙ) → Dec (Δ ⊢ₙ τₙ ∶ κ)
--   uniq-⊢ₖₙ : ∀ {Δ τ κ κ'} → Δ ⊢ₙ τ ∶ κ → Δ ⊢ₙ τ ∶ κ' → κ ≡ κ'
--   lemma₁ : ∀ {Δ τ κ} → Δ ⊢ τ ∶ κ → Δ ⊢ₙ normalizeType τ ∶ κ
--   lemma₂ : ∀ {Δ τ κ} → Δ ⊢ₙ τₙ ∶ κ → Δ ⊢ denormalizeType τₙ ∶ κ

-- mutual
--   inferTypeₙ : ∀ (Δ : KindCtx) (Γ : TypeCtxₙ) (e : Term) → Dec (∃[ τ ] Δ , Γ ⊢ e ∶ₙ τ)
--   inferTypeₙ Δ Γ (var x) with find Γ x
--   ... | no ref = no λ { ⟨ τ , var _ prf ⟩ → ref ⟨ τ , prf ⟩ }
--   ... | yes ⟨ τ , prf ⟩ with checkKindₙ Δ ⋆ τ
--   ...   | no ref = no λ { ⟨ τ' , var prfₖ prf' ⟩ → case uniq-∋ prf prf' of λ { refl → ref prfₖ } }
--   ...   | yes prfₖ = yes ⟨ τ , var prfₖ prf ⟩
--   inferTypeₙ Δ Γ (lam τ e) with checkKindₙ Δ ⋆ (normalizeType τ)
--   ... | no ref = no λ { ⟨ fun τ τ' , lam _ prf₁ _ ⟩ → ref {! prf₁  !} }
--   ... | yes prfₖ₁ with inferTypeₙ Δ (normalizeType τ ∷ Γ) e
--   ...   | no ref = no λ { ⟨ fun τ τ' , lam _ _ prf₂ ⟩ → ref ⟨ τ' , {! prf₂ !} ⟩ }
--   ...   | yes ⟨ τ' , prf₂ ⟩ with checkKindₙ Δ ⋆ τ'
--   ...     | no ref = no λ { ⟨ fun τ τ' , lam (fun _ prfₖ₂) _ prf₂' ⟩ → case uniq-⊢ₜ prf₂ {! prf₂' !} of λ { refl → ref prfₖ₂ } }
--   ...     | yes prfₖ₂ = yes ⟨ fun (normalizeType τ) τ' , lam (fun prfₖ₁ prfₖ₂) prfₖ₁ prf₂ ⟩
--   inferTypeₙ Δ Γ (app e₁ e₂) with inferTypeₙ Δ Γ e₁
--   ... | no ref = no λ { ⟨ τ' , app _ prf₁ _ ⟩ → ref ⟨ fun _ τ' , prf₁ ⟩ }
--   -- ... | yes ⟨ τ , prf₁ ⟩ = no λ { ⟨ τ , app _ prf₁' _ ⟩ → case (uniq-⊢ₜ prf₁ prf₁') of {!   !} }
--   ... | yes ⟨ fun τ τ' , prf₁ ⟩ with checkTypeₙ Δ Γ τ e₂
--   ...   | no ref = no λ { ⟨ τ , app _ prf₁' prf₂ ⟩ → case uniq-⊢ₜ prf₁ prf₁' of λ { refl → ref prf₂ } }
--   ...   | yes prf₂ with checkKindₙ Δ ⋆ τ'
--   ...     | no ref = no λ { ⟨ τ , app prfₖ prf₁' _ ⟩ → case uniq-⊢ₜ prf₁ prf₁' of λ { refl → ref prfₖ } }
--   ...     | yes prfₖ = yes ⟨ τ' , app prfₖ prf₁ prf₂ ⟩
--   inferTypeₙ Δ Γ (tlam κ e) with inferTypeₙ (κ ∷ Δ) Γ e
--   ... | no ref = no λ { ⟨ all κ τ , tlam _ prf ⟩ → ref ⟨ τ , prf ⟩ }
--   ... | yes ⟨ τ , prf ⟩ with checkKindₙ (κ ∷ Δ) ⋆ τ
--   ...   | no ref = no λ { ⟨ all κ τ , tlam (all prfₖ) prf' ⟩ → case uniq-⊢ₜ prf prf' of λ { refl → ref prfₖ } }
--   ...   | yes prfₖ = yes ⟨ all κ τ , tlam (all prfₖ) prf ⟩
--   inferTypeₙ Δ Γ (tapp e τₛ) with inferTypeₙ Δ Γ e
--   ... | no ref = no λ { ⟨ τ , tapp _ prf prfₖ ⟩ → ref ⟨ all _ _ , prf ⟩ }
--   -- ... | yes ⟨ τ' , prf ⟩ = no {!   !}
--   ... | yes ⟨ all κ τ , prf ⟩ with checkKindₙ Δ κ (normalizeType τₛ)
--   ...   | no ref = no λ { ⟨ τ , tapp _ prf' prfₖ ⟩ → case uniq-⊢ₜ prf prf' of λ { refl → ref prfₖ } }
--   ...   | yes prfₖₛ with checkKindₙ (κ ∷ Δ) ⋆ τ
--   ...     | no ref = no λ { _ → case prf of λ { (tlam (all prfₖ) _) → ref prfₖ } }
--   ...     | yes prfₖ = yes ⟨ τ [ normalizeType τₛ ]ₙ , tapp (substTypingHereₙ prfₖ prfₖₛ) prf prfₖₛ ⟩

--   checkTypeₙ : ∀ (Δ : KindCtx) (Γ : TypeCtxₙ) (τ : Typeₙ) (e : Term) → Dec (Δ , Γ ⊢ e ∶ₙ τ)
--   checkTypeₙ Δ Γ τ e with inferTypeₙ Δ Γ e
--   ... | no ref = no λ prf → ref ⟨ τ , prf ⟩
--   ... | yes ⟨ τ' , prf ⟩ with τ' ≟ₜ τ
--   ...   | no ref   = no λ prf' → ref (uniq-⊢ₜ prf prf')
--   ...   | yes refl = yes prf


-- inferType : ∀ (Δ : KindCtx) (Γ : TypeCtx) (e : Term) → Dec (∃[ τ ] Δ , Γ ⊢ e ∶ τ)
-- inferType Δ Γ e with inferTypeₙ Δ (normalizeTypeCtx Γ) e
-- ... | no ref = no λ { ⟨ τ , prf ⟩ → ref ⟨ normalizeType τ , normalizeTyping prf ⟩ }
-- ... | yes ⟨ τₙ , prfₙ ⟩ = yes ⟨ denormalizeType τₙ , denormalizeTyping prfₙ ⟩