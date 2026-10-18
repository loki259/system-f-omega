module Type.Equality where

open import Prelude
open import Type
open import Type.Context
open import Type.Kinding
open import Type.Substitution


infix 3 _⊢_≡ₜ_∶_
data _⊢_≡ₜ_∶_ (Δ : KindCtx) : Type → Type → Kind → Set where
  trefl : Δ ⊢ τ ∶ κ → Δ ⊢ τ ≡ₜ τ ∶ κ
  tsym : Δ ⊢ τ₁ ≡ₜ τ₂ ∶ κ → Δ ⊢ τ₂ ≡ₜ τ₁ ∶ κ
  ttrans : Δ ⊢ τ₁ ≡ₜ τ₂ ∶ κ → Δ ⊢ τ₂ ≡ₜ τ₃ ∶ κ → Δ ⊢ τ₁ ≡ₜ τ₃ ∶ κ
  fun : Δ ⊢ τ₁ ≡ₜ τ₁' ∶ ⋆ → Δ ⊢ τ₂ ≡ₜ τ₂' ∶ ⋆ → Δ ⊢ fun τ₁ τ₂ ≡ₜ fun τ₁' τ₂' ∶ ⋆
  all : κ ∷ Δ ⊢ τ ≡ₜ τ' ∶ ⋆ → Δ ⊢ all κ τ ≡ₜ all κ τ' ∶ ⋆
  lam : κ ∷ Δ ⊢ τ ≡ₜ τ' ∶ κ' → Δ ⊢ lam κ τ ≡ₜ lam κ τ' ∶ κ ⇒ κ'
  app : Δ ⊢ τ₁ ≡ₜ τ₁' ∶ κ ⇒ κ' → Δ ⊢ τ₂ ≡ₜ τ₂' ∶ κ → Δ ⊢ app τ₁ τ₂ ≡ₜ app τ₁' τ₂' ∶ κ'
  beta : Δ ⊢ app (lam κ τ) τₛ ∶ κ' → Δ ⊢ app (lam κ τ) τₛ ≡ₜ τ [ τₛ ] ∶ κ'
  eta : Δ ⊢ τ ∶ κ ⇒ κ' → Δ ⊢ τ ≡ₜ lam κ (app (weakenType τ) (var zero)) ∶ κ ⇒ κ'


extractKindingFromEquality : Δ ⊢ τ ≡ₜ τ' ∶ κ → Δ ⊢ τ ∶ κ × Δ ⊢ τ' ∶ κ
extractKindingFromEquality (trefl prf)                 = ⟨ prf , prf ⟩
extractKindingFromEquality (tsym eq)                   = swap (extractKindingFromEquality eq)
extractKindingFromEquality (ttrans eq₁ eq₂)            = ⟨ extractKindingFromEquality eq₁ .proj₁ , extractKindingFromEquality eq₂ .proj₂ ⟩
extractKindingFromEquality (beta (app (lam prf) prfₛ)) = ⟨ app (lam prf) prfₛ , substKindingHere prf prfₛ ⟩
extractKindingFromEquality (eta prf)                   = ⟨ prf , lam (app (weakenKinding prf) (var here)) ⟩
extractKindingFromEquality (fun eq₁ eq₂)               = Σ-zip fun fun (extractKindingFromEquality eq₁) (extractKindingFromEquality eq₂)
extractKindingFromEquality (app eq₁ eq₂)               = Σ-zip app app (extractKindingFromEquality eq₁) (extractKindingFromEquality eq₂)
extractKindingFromEquality (all eq)                    = Σ-map all all (extractKindingFromEquality eq)
extractKindingFromEquality (lam eq)                    = Σ-map lam lam (extractKindingFromEquality eq)