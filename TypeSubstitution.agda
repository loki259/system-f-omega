module TypeSubstitution where

open import Prelude
open import Syntax
open import Context
open import Kinding


renameType : ∀ {Φ Ψ} → Renaming Φ Ψ → ∀ {τ κ} → Φ ⊢ τ ∶ κ → ∃[ τ' ] Ψ ⊢ τ' ∶ κ
renameType ρ (var prf)       = Σ-map var var (ρ prf)
renameType ρ (lam prf)       = Σ-map (lam _) lam (renameType (lift ρ) prf)
renameType ρ (app prf₁ prf₂) = Σ-zip app app (renameType ρ prf₁) (renameType ρ prf₂)
renameType ρ (fun prf₁ prf₂) = Σ-zip fun fun (renameType ρ prf₁) (renameType ρ prf₂)
renameType ρ (all prf)       = Σ-map (all _) all (renameType (lift ρ) prf)

weakenType : ∀ {Φ κ κ' τ} → Φ ⊢ τ ∶ κ → ∃[ τ' ] κ' ∷ Φ ⊢ τ' ∶ κ
weakenType = renameType λ prf → -, there prf


TypeSubst : KindCtx → KindCtx → Set
TypeSubst Φ Ψ = ∀ {x κ} → Φ ∋ x ↦ κ → ∃[ τ ] Ψ ⊢ τ ∶ κ

liftTypeSubst : ∀ {Φ Ψ} → TypeSubst Φ Ψ → ∀ {κ} → TypeSubst (κ ∷ Φ) (κ ∷ Ψ)
liftTypeSubst σ here        = ⟨ var zero , var here ⟩   -- Leave newly bound variable untouched
liftTypeSubst σ (there prf) = weakenType (σ prf .proj₂) -- Apply substitution and weakenType

substType : ∀ {Φ Ψ} → TypeSubst Φ Ψ → ∀ {κ τ} → Φ ⊢ τ ∶ κ → ∃[ τ' ] Ψ ⊢ τ' ∶ κ
substType σ (var prf)       = σ prf
substType σ (lam prf)       = Σ-map (lam _) lam (substType (liftTypeSubst σ) prf)
substType σ (app prf₁ prf₂) = Σ-zip app app (substType σ prf₁) (substType σ prf₂)
substType σ (fun prf₁ prf₂) = Σ-zip fun fun (substType σ prf₁) (substType σ prf₂)
substType σ (all prf)       = Σ-map (all _) all (substType (liftTypeSubst σ) prf)

extendTypeSubst : ∀ {Φ Ψ} → TypeSubst Φ Ψ → ∀ {κ τ} → Ψ ⊢ τ ∶ κ → TypeSubst (κ ∷ Φ) Ψ
extendTypeSubst σ prf here        = -, prf -- Project out additional term
extendTypeSubst σ _   (there prf) = σ prf  -- Apply original substitution

infix 5 _[_]
_[_] : ∀ {Φ κ κ' τ τ'} → κ ∷ Φ ⊢ τ' ∶ κ' → Φ ⊢ τ ∶ κ → ∃[ τ'' ] Φ ⊢ τ'' ∶ κ'
τ' [ τ ] = substType (extendTypeSubst (λ prf → -, var prf) τ) τ'

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