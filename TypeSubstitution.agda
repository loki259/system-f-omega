{-# OPTIONS --allow-unsolved-metas #-}

module TypeSubstitution where

open import Prelude
open import Syntax
open import Context
open import Kinding


IndexRenaming : Set
IndexRenaming = Nat → Nat

liftIndexRenaming : IndexRenaming → IndexRenaming
liftIndexRenaming f zero    = zero
liftIndexRenaming f (suc x) = suc (f x)

renameType : IndexRenaming → Type → Type
renameType f (var x)     = var (f x)
renameType f (fun τ₁ τ₂) = fun (renameType f τ₁) (renameType f τ₂)
renameType f (lam x τ)   = lam x (renameType (liftIndexRenaming f) τ)
renameType f (app τ₁ τ₂) = app (renameType f τ₁) (renameType f τ₂)
renameType f (all x τ)   = all x (renameType (liftIndexRenaming f) τ)

Renaming : ∀ {A} → Ctx A → Ctx A → IndexRenaming → Set
Renaming {A} Φ Ψ f = ∀ {x a} → Φ ∋ x ↦ a → Ψ ∋ f x ↦ a

liftRenaming : ∀ {A Φ Ψ f} → Renaming {A} Φ Ψ f → ∀ {a'} → Renaming {A} (a' ∷ Φ) (a' ∷ Ψ) (liftIndexRenaming f)
liftRenaming ρ here        = here
liftRenaming ρ (there prf) = there (ρ prf)

renameTyping : ∀ {Φ Ψ f} → Renaming Φ Ψ f → ∀ {τ κ} → Φ ⊢ τ ∶ κ → Ψ ⊢ renameType f τ ∶ κ
renameTyping ρ (var prf)       = var (ρ prf)
renameTyping ρ (fun prf₁ prf₂) = fun (renameTyping ρ prf₁) (renameTyping ρ prf₂)
renameTyping ρ (all prf)       = all (renameTyping (liftRenaming ρ) prf)
renameTyping ρ (lam prf)       = lam (renameTyping (liftRenaming ρ) prf)
renameTyping ρ (app prf₁ prf₂) = app (renameTyping ρ prf₁) (renameTyping ρ prf₂)

weakenType : Type → Type
weakenType τ = renameType suc τ

weakenTyping : ∀ {Φ κ κ' τ} → Φ ⊢ τ ∶ κ → κ' ∷ Φ ⊢ weakenType τ ∶ κ
weakenTyping prf = renameTyping there prf

TypeSubst : Set
TypeSubst = Nat → Type

liftTypeSubst : TypeSubst → TypeSubst
liftTypeSubst f zero    = var zero
liftTypeSubst f (suc x) = weakenType (f x)

substType : TypeSubst → Type → Type
substType f (var x)     = f x
substType f (fun τ₁ τ₂) = fun (substType f τ₁) (substType f τ₂)
substType f (lam x τ)   = lam x (substType (liftTypeSubst f) τ)
substType f (app τ₁ τ₂) = app (substType f τ₁) (substType f τ₂)
substType f (all x τ)   = all x (substType (liftTypeSubst f) τ)

TypingSubst : KindCtx → KindCtx → TypeSubst → Set
TypingSubst Φ Ψ f = ∀ {x κ} → Φ ∋ x ↦ κ → Ψ ⊢ f x ∶ κ

liftTypingSubst : ∀ {Φ Ψ f} → TypingSubst Φ Ψ f → ∀ {κ} → TypingSubst (κ ∷ Φ) (κ ∷ Ψ) (liftTypeSubst f)
liftTypingSubst σ here        = var here
liftTypingSubst σ (there prf) = weakenTyping (σ prf)

substTyping : ∀ {Φ Ψ f} → TypingSubst Φ Ψ f → ∀ {κ τ} → Φ ⊢ τ ∶ κ → Ψ ⊢ substType f τ ∶ κ
substTyping σ (var prf)       = σ prf
substTyping σ (lam prf)       = lam (substTyping (liftTypingSubst σ) prf)
substTyping σ (app prf₁ prf₂) = app (substTyping σ prf₁) (substTyping σ prf₂)
substTyping σ (fun prf₁ prf₂) = fun (substTyping σ prf₁) (substTyping σ prf₂)
substTyping σ (all prf)       = all (substTyping (liftTypingSubst σ) prf)

extendTypeSubst : TypeSubst → Type → TypeSubst
extendTypeSubst f τ zero    = τ
extendTypeSubst f τ (suc x) = f x

extendTypingSubst : ∀ {Φ Ψ f} → TypingSubst Φ Ψ f → ∀ {κ τ} → Ψ ⊢ τ ∶ κ → TypingSubst (κ ∷ Φ) Ψ (extendTypeSubst f τ)
extendTypingSubst σ prf here        = prf
extendTypingSubst σ _   (there prf) = σ prf

substTypeAtZero : Type → Type → Type
substTypeAtZero τ τₛ = substType (extendTypeSubst var τₛ) τ

infix 5 _[_]
_[_] : Type → Type → Type
τ [ τₛ ] = substTypeAtZero τ τₛ

substTypingHere : ∀ {Φ κ κ' τ τₛ} → κ ∷ Φ ⊢ τ ∶ κ' → Φ ⊢ τₛ ∶ κ → Φ ⊢ τ [ τₛ ] ∶ κ'
substTypingHere prf prfₛ = substTyping (extendTypingSubst var prfₛ) prf


-- lift-id : ∀ {Φ J K} (α : K ∷ Φ ∋ J) → lift id α ≡ α
-- lift⋆-comp : ∀ {Φ Ψ Θ} {ρ : TypeRenaming Φ Ψ} {ρ' : TypeRenaming Ψ Θ} {J K} (α : K ∷ Φ ∋ J)
--            → lift (ρ' ◦ ρ) α ≡ lift ρ' (lift ρ α)

-- renameType-id : ∀ {Φ J} (A : Φ ⊢ J) → renameType id A ≡ A
-- renameType-comp : ∀ {Φ Ψ Θ} {ρ : TypeRenaming Φ Ψ} {ρ' : TypeRenaming Ψ Θ} {J} (A : Φ ⊢ J)
--          → renameType (ρ' ◦ ρ) A ≡ renameType ρ' (renameType ρ A)

-- liftTypeSubst-id : ∀ {Φ J K} (x : K ∷ Φ ∋ J) → liftTypeSubst var x ≡ var x
-- liftTypeSubst-comp : ∀ {Φ Ψ Θ} {σ : TypeSubst Φ Ψ} {σ' : TypeSubst Ψ Θ} {J K} (α : K ∷ Φ ∋ J)
--            → liftTypeSubst (substType σ' ◦ σ) α ≡ substType (liftTypeSubst σ') (liftTypeSubst σ α)

-- substType-id : ∀ {Φ J} (A : Φ ⊢ J) → substType var A ≡ A
-- substType-var : ∀ {Φ Ψ} {σ : TypeSubst Φ Ψ} {J} (α : Φ ∋ J) → substType σ (var α) ≡ σ α
-- substType-comp : ∀ {Φ Ψ Θ} {σ : TypeSubst Φ Ψ} {σ' : TypeSubst Ψ Θ} {J} (A : Φ ⊢ J)
--          → substType (substType σ' ◦ σ) A ≡ substType σ’ (substType σ A)
