{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --allow-incomplete-matches #-}

module Term.Typing where

open import Prelude
open import Term
open import Type.Kinding
open import Type.Substitution
open import Term.Context


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