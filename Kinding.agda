{-# OPTIONS --allow-unsolved-metas #-}

module Kinding where

open import Relation.Binary.Definitions using (DecidableEquality)
open import Prelude
open import Syntax


KindCtx : Set
KindCtx = Ctx Kind

variable
  Δ : KindCtx

infix 3 _⊢_∶_
data _⊢_∶_ (Δ : KindCtx) : Type → Kind → Set where
  var : ∀ {x κ} → Δ ∋ x ↦ κ → Δ ⊢ var x ∶ κ
  fun : ∀ {τ τ'} → Δ ⊢ τ ∶ ⋆ → Δ ⊢ τ' ∶ ⋆ → Δ ⊢ fun τ τ' ∶ ⋆
  all : ∀ {κ τ} → κ ∷ Δ ⊢ τ ∶ ⋆ → Δ ⊢ all κ τ ∶ ⋆
  lam : ∀ {κ κ' τ} → κ ∷ Δ ⊢ τ ∶ κ' → Δ ⊢ lam κ τ ∶ tfun κ κ'
  app : ∀ {τ τ' κ κ'} → Δ ⊢ τ ∶ tfun κ κ' → Δ ⊢ τ' ∶ κ → Δ ⊢ app τ τ' ∶ κ'


_≟ₖ_ : DecidableEquality Kind
⋆ ≟ₖ ⋆ = yes refl
tfun κ₁ κ₁' ≟ₖ tfun κ₂ κ₂' with κ₁ ≟ₖ κ₂
... | no ref = no λ { refl → ref refl }
... | yes refl with κ₁' ≟ₖ κ₂'
...   | no ref   = no λ { refl → ref refl }
...   | yes refl = yes refl
⋆ ≟ₖ tfun _ _ = no λ ()
tfun _ _ ≟ₖ ⋆ = no λ ()


dom≡ : ∀ {κ₁ κ₁' κ₂ κ₂'} → tfun κ₁ κ₂ ≡ tfun κ₁' κ₂' → κ₁ ≡ κ₁'
dom≡ refl = refl

rng≡ : ∀ {κ₁ κ₁' κ₂ κ₂'} → tfun κ₁ κ₂ ≡ tfun κ₁' κ₂' → κ₂ ≡ κ₂'
rng≡ refl = refl

uniq-∋ : ∀ {A x a b} {ctx : Ctx A} → ctx ∋ x ↦ a → ctx ∋ x ↦ b → a ≡ b
uniq-∋ here         here         = refl
uniq-∋ (there prf₁) (there prf₂) = uniq-∋ prf₁ prf₂

uniq-⊢ : ∀ {Δ x a b} → Δ ⊢ x ∶ a → Δ ⊢ x ∶ b → a ≡ b
uniq-⊢ (var prf₁)      (var prf₂)      = uniq-∋ prf₁ prf₂
uniq-⊢ (fun prf₁ prf₂) (fun prf₃ prf₄) = refl
uniq-⊢ (all prf₁)      (all prf₂)      = refl
uniq-⊢ (lam prf₁)      (lam prf₂)      = cong (tfun _) (uniq-⊢ prf₁ prf₂)
uniq-⊢ (app prf₁ _)    (app prf₃ _)    = rng≡ (uniq-⊢ prf₁ prf₃)

mutual
  checkKind : ∀ (Δ : KindCtx) (κ : Kind) (τ : Type) → Dec (Δ ⊢ τ ∶ κ)
  checkKind Δ κ τ with inferKind Δ τ
  ... | no ref = no λ prf → ref ⟨ κ , prf ⟩
  ... | yes ⟨ κ' , prf ⟩ with κ ≟ₖ κ'
  ...   | no ref   = no λ prf' → ref (uniq-⊢ prf' prf)
  ...   | yes refl = yes prf

  inferKind : ∀ (Δ : KindCtx) (τ : Type) → Dec (∃[ κ ] Δ ⊢ τ ∶ κ)
  inferKind Δ (var x) with find Δ x
  ... | yes ⟨ κ , prf ⟩ = yes ⟨ κ , var prf ⟩
  ... | no ref          = no λ { ⟨ κ , var prf ⟩ → ref ⟨ κ , prf ⟩ }
  inferKind Δ (fun τ₁ τ₂) with checkKind Δ ⋆ τ₁
  ... | no ref = no λ { ⟨ ⋆ , fun prf₁ _ ⟩ → ref prf₁ }
  ... | yes prf₁ with checkKind Δ ⋆ τ₂
  ...   | no ref   = no λ { ⟨ ⋆ , fun _ prf₂ ⟩ → ref prf₂ }
  ...   | yes prf₂ = yes ⟨ ⋆ , fun prf₁ prf₂ ⟩
  inferKind Δ (lam κ τ) with inferKind (κ ∷ Δ) τ
  ... | yes ⟨ κ' , prf ⟩ = yes ⟨ tfun κ κ' , lam prf ⟩
  ... | no ref           = no λ { ⟨ tfun κ κ' , lam prf ⟩ → ref ⟨ κ' , prf ⟩ }
  inferKind Δ (app τ₁ τ₂) with inferKind Δ τ₁
  ... | no ref           = no λ { ⟨ κ' , app prf₁ _ ⟩ → ref ⟨ tfun _ κ' , prf₁ ⟩ }
  ... | yes ⟨ ⋆ , prf₁ ⟩ = no λ { ⟨ κ , app prf₁' _ ⟩ → case (uniq-⊢ prf₁ prf₁') of λ () }
  ... | yes ⟨ tfun κ κ' , prf₁ ⟩ with checkKind Δ κ τ₂
  ...   | yes prf₂ = yes ⟨ κ' , app prf₁ prf₂ ⟩
  ...   | no ref   = no λ { ⟨ κ , app prf₁' prf₂ ⟩ → case dom≡ (uniq-⊢ prf₁ prf₁') of λ { refl → ref prf₂ } }
  inferKind Δ (all κ τ) with checkKind (κ ∷ Δ) ⋆ τ
  ... | no ref = no λ { ⟨ ⋆ , all prf ⟩ → ref prf }
  ... | yes prf = yes ⟨ ⋆ , all prf ⟩
