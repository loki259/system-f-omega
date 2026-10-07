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

infix 3 _≡ₜ_
data _≡ₜ_ : Type → Type → Set where
  trefl  : ∀ {τ} → τ ≡ₜ τ
  tsym   : ∀ {τ τ'} → τ ≡ₜ τ' → τ' ≡ₜ τ
  ttrans : ∀ {τ₁ τ₂ τ₃} → τ₁ ≡ₜ τ₂ → τ₂ ≡ₜ τ₃ → τ₁ ≡ₜ τ₃
  fun    : ∀ {τ₁ τ₁' τ₂ τ₂'} → τ₁ ≡ₜ τ₁' → τ₂ ≡ₜ τ₂' → fun τ₁ τ₂ ≡ₜ fun τ₁' τ₂'
  all    : ∀ {κ τ τ'} → τ ≡ₜ τ' → all κ τ ≡ₜ all κ τ'
  lam    : ∀ {κ τ τ'} → τ ≡ₜ τ' → lam κ τ ≡ₜ lam κ τ'
  app    : ∀ {τ₁ τ₁' τ₂ τ₂'} → τ₁ ≡ₜ τ₁' → τ₂ ≡ₜ τ₂' → app τ₁ τ₂ ≡ₜ app τ₁' τ₂'
  beta   : ∀ {κ τ τ'} → app (lam κ τ) τ' ≡ₜ instantiate τ' τ

infix 3 _,_⊢_∶_
data _,_⊢_∶_ (Δ : KindCtx) (Γ : TypeCtx) : Term → Type → Set where
  var : ∀ {x τ}
    → Γ ∋ x ↦ τ
    → Δ , Γ ⊢ var x ∶ τ
  lam : ∀ {τ τ' t}
    → Δ ⊢ τ ∶ ⋆
    → Δ , (τ ∷ Γ) ⊢ t ∶ τ'
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
  cast : ∀ {t τ τ'}
    → τ ≡ₜ τ'
    → Δ , Γ ⊢ t ∶ τ
    → Δ , Γ ⊢ t ∶ τ'


_≟ₜ_ : (τ τ' : Type) → Dec (τ ≡ₜ τ')
τ₁ ≟ₜ τ₂ = {!   !}


dom≡ₜ : ∀ {τ₁ τ₁' τ₂ τ₂'} → fun τ₁ τ₂ ≡ₜ fun τ₁' τ₂' → τ₁ ≡ₜ τ₁'
dom≡ₜ trefl = trefl
dom≡ₜ (tsym eq) = tsym (dom≡ₜ eq)
-- dom≡ₜ (ttrans eq₁ eq₂) = ttrans (dom≡ₜ eq₁) (dom≡ₜ eq₂)
dom≡ₜ (fun eq₁ _) = eq₁

rng≡ₜ : ∀ {τ₁ τ₁' τ₂ τ₂'} → fun τ₁ τ₂ ≡ₜ fun τ₁' τ₂' → τ₂ ≡ₜ τ₂'
rng≡ₜ trefl = trefl
rng≡ₜ (tsym eq) = tsym (rng≡ₜ eq)
-- rng≡ₜ (ttrans eq₁ eq₂) = ttrans (rng≡ₜ eq₁) (rng≡ₜ eq₂)
rng≡ₜ (fun _ eq₂) = eq₂

uniq-⊢ₜ : ∀ {Δ Γ e τ τ'} → Δ , Γ ⊢ e ∶ τ → Δ , Γ ⊢ e ∶ τ' → τ ≡ₜ τ'
uniq-⊢ₜ = {!   !}

mutual
  inferType : ∀ (Δ : KindCtx) (Γ : TypeCtx) (e : Term) → Dec (∃[ τ ] Δ , Γ ⊢ e ∶ τ)
  inferType Δ Γ (var x) with find Γ x
  ... | no ref          = no λ { ⟨ τ , var prf ⟩ → ref ⟨ τ , prf ⟩
                               ; ⟨ τ , cast eq prf ⟩ → ref ⟨ τ , {!   !} ⟩ }
  ... | yes ⟨ τ , prf ⟩ = yes ⟨ τ , var prf ⟩
  inferType Δ Γ (lam τ e) with checkKind Δ ⋆ τ
  ... | no ref = no λ { ⟨ fun τ τ' , lam prf₁ prf₂ ⟩ → ref prf₁ }
  ... | yes prf₁ with inferType Δ (τ ∷ Γ) e
  ...   | no ref            = no λ { ⟨ fun τ τ' , lam prf₁ prf₂ ⟩ → ref ⟨ τ' , prf₂ ⟩ }
  ...   | yes ⟨ τ' , prf₂ ⟩ = yes ⟨ fun τ τ' , lam prf₁ prf₂ ⟩
  inferType Δ Γ (app e₁ e₂) with inferType Δ Γ e₁
  ... | no ref           = no λ { ⟨ τ' , app prf₁ _ ⟩ → ref ⟨ fun _ τ' , prf₁ ⟩ }
  ... | yes ⟨ τ , prf₁ ⟩ = no λ { ⟨ τ , app prf₁' _ ⟩ → case (uniq-⊢ₜ prf₁ prf₁') of λ () }
  ... | yes ⟨ fun τ τ' , prf₁ ⟩ with checkType Δ Γ τ e₂
  ...   | no ref   = no λ { ⟨ τ , app prf₁' prf₂ ⟩ → case dom≡ₜ (uniq-⊢ₜ prf₁' prf₁) of λ { eq → ref (cast eq prf₂) } }
  ...   | yes prf₂ = yes ⟨ τ' , app prf₁ prf₂ ⟩
  inferType Δ Γ (tlam κ e) with inferType (κ ∷ Δ) (weaken Γ) e
  ... | no ref          = no λ { ⟨ all κ τ , tlam prf ⟩ → ref ⟨ τ , prf ⟩ }
  ... | yes ⟨ τ , prf ⟩ = yes ⟨ all κ τ , tlam prf ⟩
  inferType Δ Γ (tapp e τ) with inferType Δ Γ e
  ... | no ref            = no λ { ⟨ τ , tapp prf₁ prf₂ ⟩ → ref {!   !} }
  ... | yes ⟨ τ' , prf₁ ⟩ = {!   !}
  ... | yes ⟨ all κ τ' , prf₁ ⟩ with checkKind Δ κ τ
  ...   | no ref   = {!   !}
  ...   | yes prf₂ = {! yes ⟨ instantiate τ τ' , tapp prf₁ prf₂ ⟩ !}

  checkType : ∀ (Δ : KindCtx) (Γ : TypeCtx) (τ : Type) (e : Term) → Dec (Δ , Γ ⊢ e ∶ τ)
  checkType Δ Γ τ e with inferType Δ Γ e
  ... | no ref = no λ prf → ref ⟨ τ , prf ⟩
  ... | yes ⟨ τ' , prf ⟩ with τ' ≟ₜ τ
  ...   | no ref   = no λ prf' → ref (uniq-⊢ₜ prf prf')
  ...   | yes eq = yes (cast eq prf)