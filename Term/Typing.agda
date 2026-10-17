{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --allow-incomplete-matches #-}

module Term.Typing where

open import Prelude
open import Term
open import Term.Context
open import Type.Kinding
open import Type.Substitution
open import Type.Equality

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