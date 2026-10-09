{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --allow-incomplete-matches #-}

module Typing where

open import Prelude
open import Syntax
open import Context
open import Kinding
open import TypeSubstitution


TypeCtx : Set
TypeCtx = Ctx Type

variable
  Γ : TypeCtx


infix 3 _⊢_≡ₜ_∶_
data _⊢_≡ₜ_∶_ (Δ : KindCtx) : Type → Type → Kind → Set where
  trefl : ∀ {τ κ}
    → Δ ⊢ τ ∶ κ
    → Δ ⊢ τ ≡ₜ τ ∶ κ
  tsym : ∀ {τ₁ τ₂ κ}
    → Δ ⊢ τ₁ ∶ κ
    → Δ ⊢ τ₂ ∶ κ
    → Δ ⊢ τ₁ ≡ₜ τ₂ ∶ κ
    → Δ ⊢ τ₂ ≡ₜ τ₁ ∶ κ
  ttrans : ∀ {τ₁ τ₂ τ₃}
    → Δ ⊢ τ₁ ∶ κ
    → Δ ⊢ τ₂ ∶ κ
    → Δ ⊢ τ₃ ∶ κ
    → Δ ⊢ τ₁ ≡ₜ τ₂ ∶ κ
    → Δ ⊢ τ₂ ≡ₜ τ₃ ∶ κ
    → Δ ⊢ τ₁ ≡ₜ τ₃ ∶ κ
  fun : ∀ {τ₁ τ₁' τ₂ τ₂'}
    → Δ ⊢ fun τ₁ τ₂ ∶ ⋆
    → Δ ⊢ fun τ₁' τ₂' ∶ ⋆
    → Δ ⊢ τ₁ ≡ₜ τ₁' ∶ ⋆
    → Δ ⊢ τ₂ ≡ₜ τ₂' ∶ ⋆
    → Δ ⊢ fun τ₁ τ₂ ≡ₜ fun τ₁' τ₂' ∶ ⋆
  all : ∀ {κ τ τ'}
    → Δ ⊢ all κ τ ∶ ⋆
    → Δ ⊢ all κ τ' ∶ ⋆
    → κ ∷ Δ ⊢ τ ≡ₜ τ' ∶ ⋆
    → Δ ⊢ all κ τ ≡ₜ all κ τ' ∶ ⋆
  lam : ∀ {κ κ' τ τ'}
    → Δ ⊢ lam κ τ ∶ tfun κ κ'
    → Δ ⊢ lam κ τ' ∶ tfun κ κ'
    → κ ∷ Δ ⊢ τ ≡ₜ τ' ∶ κ'
    → Δ ⊢ lam κ τ ≡ₜ lam κ τ' ∶ tfun κ κ'
  app : ∀ {κ κ' τ₁ τ₁' τ₂ τ₂'}
    → Δ ⊢ app τ₁ τ₂ ∶ κ'
    → Δ ⊢ app τ₁' τ₂' ∶ κ'
    → Δ ⊢ τ₁ ≡ₜ τ₁' ∶ tfun κ κ'
    → Δ ⊢ τ₂ ≡ₜ τ₂' ∶ κ
    → Δ ⊢ app τ₁ τ₂ ≡ₜ app τ₁' τ₂' ∶ κ'
  beta : ∀ {κ κ' τ τₛ}
    → Δ ⊢ app (lam κ τ) τₛ ∶ κ'
    → Δ ⊢ τ [ τₛ ] ∶ κ'
    → Δ ⊢ app (lam κ τ) τₛ ≡ₜ τ [ τₛ ] ∶ κ'

infix 3 _,_⊢_∶_
data _,_⊢_∶_ (Δ : KindCtx) (Γ : TypeCtx) : Term → Type → Set where
  var : ∀ {x τ}
    → Δ ⊢ τ ∶ ⋆
    → Γ ∋ x ↦ τ
    → Δ , Γ ⊢ var x ∶ τ
  lam : ∀ {τ τ' t}
    → Δ ⊢ fun τ τ' ∶ ⋆
    → Δ ⊢ τ ∶ ⋆
    → Δ , (τ ∷ Γ) ⊢ t ∶ τ'
    → Δ , Γ ⊢ lam τ t ∶ fun τ τ'
  app : ∀ {τ τ' t t'}
    → Δ ⊢ τ' ∶ ⋆
    → Δ , Γ ⊢ t ∶ fun τ τ'
    → Δ , Γ ⊢ t' ∶ τ
    → Δ , Γ ⊢ app t t' ∶ τ'
  tlam : ∀ {κ τ t}
    → Δ ⊢ all κ τ ∶ ⋆
    → κ ∷ Δ , Γ ⊢ t ∶ τ
    → Δ , Γ ⊢ tlam κ t ∶ all κ τ
  tapp : ∀ {κ τ t τₛ}
    → Δ ⊢ τ [ τₛ ] ∶ ⋆
    → Δ , Γ ⊢ t ∶ all κ τ
    → Δ ⊢ τₛ ∶ κ
    → Δ , Γ ⊢ tapp t τₛ ∶ τ [ τₛ ]
  cast : ∀ {κ τ τ' t}
    → Δ ⊢ τ ≡ₜ τ' ∶ κ
    → Δ , Γ ⊢ t ∶ τ
    → Δ , Γ ⊢ t ∶ τ'

  -- presupposition : ∀ {Δ Γ t τ} → Δ , Γ ⊢ t ∶ τ → Δ ⊢ τ ∶ ⋆
  -- presupposition (var x x₁) = x₁
  -- presupposition (lam x d x₁) = x₁
  -- presupposition (app d d₁ x) = x
  -- presupposition (tlam d x) = x
  -- presupposition (tapp d b x) = x
  -- presupposition (cast x d) = lemmaCastKinding x (presupposition d)


_⊢_≟ₜ_ : {κ : Kind} (Δ : KindCtx) (τ τ' : Type) → Dec (Δ ⊢ τ ≡ₜ τ' ∶ κ)
Δ ⊢ τ₁ ≟ₜ τ₂ = {!   !}

--_≟ₜ_ : (τ τ' : Type) → Dec (Δ ⊢ τ ≡ₜ τ')
--τ₁ ≟ₜ τ₂ = {!   !}

dom≡ₜ : ∀ {Δ τ₁ τ₁' τ₂ τ₂'} → Δ ⊢ fun τ₁ τ₂ ≡ₜ fun τ₁' τ₂' ∶ ⋆ → Δ ⊢ τ₁ ≡ₜ τ₁' ∶ ⋆
dom≡ₜ = {!!}
--dom≡ₜ trefl = trefl
--dom≡ₜ (tsym eq) = tsym (dom≡ₜ eq)
--dom≡ₜ (ttrans eq₁ eq₂) = {! !}
--dom≡ₜ (fun eq₁ _) = eq₁

rng≡ₜ : ∀ {Δ τ₁ τ₁' τ₂ τ₂'} → Δ ⊢ fun τ₁ τ₂ ≡ₜ fun τ₁' τ₂' ∶ ⋆ → Δ ⊢ τ₂ ≡ₜ τ₂' ∶ ⋆
rng≡ₜ = {!!}
--rng≡ₜ trefl = trefl
--rng≡ₜ (tsym eq) = tsym (rng≡ₜ eq)
--rng≡ₜ (ttrans eq₁ eq₂) = {!   !}
--rng≡ₜ (fun _ eq₂) = eq₂

uniq-⊢ₜ : ∀ {Δ Γ t τ τ'} → Δ , Γ ⊢ t ∶ τ → Δ , Γ ⊢ t ∶ τ' → Δ ⊢ τ ≡ₜ τ' ∶ ⋆
uniq-⊢ₜ = {!   !}

decFun : (Δ : KindCtx) → (τ : Type) → Dec (∃[ τ₁ ] ∃[ τ₂ ] Δ ⊢ τ ≡ₜ fun τ₁ τ₂ ∶ ⋆)
decFun Δ τ = {!   !}

decAll : (Δ : KindCtx) → (τ : Type) → Dec (∃[ κ ] ∃[ τ' ] Δ ⊢ τ ≡ₜ all κ τ' ∶ ⋆)
decAll Δ τ = {!   !}


-- mutual
--   inferType : ∀ (Δ : KindCtx) (Γ : TypeCtx) (e : Term) → Dec (∃[ τ ] Δ , Γ ⊢ e ∶ τ)
--   inferType Δ Γ (var x) with find Γ x
--   ... | no ref          = no λ { ⟨ τ , var _ prf ⟩ → ref ⟨ τ , prf ⟩
--                                ; ⟨ τ , cast eq prf ⟩ → ref ⟨ τ , {!   !} ⟩ }
--   ... | yes ⟨ τ , prf ⟩ with checkKind Δ ⋆ τ
--   ...   | no ref           = {!   !}
--   ...   | yes prfₖ = yes ⟨ τ , var prfₖ prf ⟩
--   inferType Δ Γ (lam τ e) with checkKind Δ ⋆ τ
--   ... | no ref = no λ { ⟨ fun τ τ' , lam _ prf₁ prf₂ ⟩ → ref prf₁ }
--   ... | yes prfₖ₁ with inferType Δ (τ ∷ Γ) e
--   ...   | no ref            = no λ { ⟨ fun τ τ' , lam _ prf₁ prf₂ ⟩ → ref ⟨ τ' , prf₂ ⟩ }
--   ...   | yes ⟨ τ' , prf₂ ⟩ with checkKind Δ ⋆ τ'
--   ...     | no ref = {!   !}
--   ...     | yes prfₖ₂ = yes ⟨ fun τ τ' , lam (fun prfₖ₁ prfₖ₂) prfₖ₁ prf₂ ⟩
--   inferType Δ Γ (app e₁ e₂) with inferType Δ Γ e₁
--   ... | no ref           = no λ { ⟨ τ' , app _ prf₁ _ ⟩ → ref ⟨ fun _ τ' , prf₁ ⟩ }
--   -- ... | yes ⟨ τ , prf₁ ⟩ = no λ { ⟨ τ , app _ prf₁' _ ⟩ → case (uniq-⊢ₜ prf₁ prf₁') of {!   !} }
--   ... | yes ⟨ fun τ τ' , prf₁ ⟩ with checkType Δ Γ τ e₂
--   ...   | no ref   = no λ { ⟨ τ , app _ prf₁' prf₂ ⟩ → case dom≡ₜ (uniq-⊢ₜ prf₁' prf₁) of λ { eq → ref (cast eq prf₂) } }
--   ...   | yes prf₂ with checkKind Δ ⋆ τ'
--   ...     | no ref = {!   !}
--   ...     | yes prfₖ = yes ⟨ τ' , app prfₖ prf₁ prf₂ ⟩
--   inferType Δ Γ (tlam κ e) with inferType (κ ∷ Δ) Γ e
--   ... | no ref          = no λ { ⟨ all κ τ , tlam _ prf ⟩ → ref ⟨ τ , prf ⟩ }
--   ... | yes ⟨ τ , prf ⟩ with checkKind (κ ∷ Δ) ⋆ τ
--   ...   | no ref = {!   !}
--   ...   | yes prfₖ = yes ⟨ all κ τ , tlam (all prfₖ) prf ⟩
--   inferType Δ Γ (tapp e τₛ) with inferType Δ Γ e
--   ... | no ref            = no λ { ⟨ τ , tapp _ prf prfₖ ⟩ → ref {!   !} }
--   -- ... | yes ⟨ τ' , prf ⟩ = no {!   !}
--   ... | yes ⟨ all κ τ , prf ⟩ with checkKind Δ κ τₛ
--   ...   | no ref   = {!   !}
--   ...   | yes prfₖₛ with checkKind (κ ∷ Δ) ⋆ τ
--   ...     | no ref = {!   !}
--   ...     | yes prfₖ = yes ⟨ τ [ τₛ ] , tapp (substTypingHere prfₖ prfₖₛ) prf prfₖₛ ⟩

--   checkType : ∀ (Δ : KindCtx) (Γ : TypeCtx) (τ : Type) (e : Term) → Dec (Δ , Γ ⊢ e ∶ τ)
--   checkType Δ Γ τ e with inferType Δ Γ e
--   ... | no ref = no λ prf → ref ⟨ τ , prf ⟩
--   ... | yes ⟨ τ' , prf ⟩ with Δ ⊢ τ' ≟ₜ τ
--   ...   | no ref   = no λ prf' → ref (uniq-⊢ₜ prf prf')
--   ...   | yes eq = yes (cast eq prf)