{-# OPTIONS --allow-unsolved-metas #-}

module TypeSubstitution where

open import Prelude
open import Syntax
open import Context
open import Kinding
open import TypeNormalization
open import Data.Sum

--------------------------------------------------------------------------------
-- Syntax
--------------------------------------------------------------------------------

renameType : IndexRenaming → Type → Type
renameType f (var x)     = var (f x)
renameType f (fun τ₁ τ₂) = fun (renameType f τ₁) (renameType f τ₂)
renameType f (lam x τ)   = lam x (renameType (liftIndexRenaming f) τ)
renameType f (app τ₁ τ₂) = app (renameType f τ₁) (renameType f τ₂)
renameType f (all x τ)   = all x (renameType (liftIndexRenaming f) τ)

weakenType : Type → Type
weakenType τ = renameType suc τ


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

extendTypeSubst : TypeSubst → Type → TypeSubst
extendTypeSubst f τ zero    = τ
extendTypeSubst f τ (suc x) = f x

substTypeAtZero : Type → Type → Type
substTypeAtZero τ τₛ = substType (extendTypeSubst var τₛ) τ

infix 5 _[_]
_[_] : Type → Type → Type
τ [ τₛ ] = substTypeAtZero τ τₛ


--------------------------------------------------------------------------------
-- Syntax (normal)
--------------------------------------------------------------------------------

mutual
  renameTypeₙ : IndexRenaming → Typeₙ → Typeₙ
  renameTypeₙ f (neu τᵤ)    = neu (renameTypeᵤ f τᵤ)
  renameTypeₙ f (fun τ₁ τ₂) = fun (renameTypeₙ f τ₁) (renameTypeₙ f τ₂)
  renameTypeₙ f (lam x τ)   = lam x (renameTypeₙ (liftIndexRenaming f) τ)
  renameTypeₙ f (all x τ)   = all x (renameTypeₙ (liftIndexRenaming f) τ)

  renameTypeᵤ : IndexRenaming → Typeᵤ → Typeᵤ
  renameTypeᵤ f (var x)     = var (f x)
  renameTypeᵤ f (app τ₁ τ₂) = app (renameTypeᵤ f τ₁) (renameTypeₙ f τ₂)

weakenTypeₙ : Typeₙ → Typeₙ
weakenTypeₙ τ = renameTypeₙ suc τ


-- TypeSubstₙ : Set
-- TypeSubstₙ = Nat → Typeₙ

-- -- TypeSubstᵤ : Set
-- -- TypeSubstᵤ = Nat → Typeᵤ

-- liftTypeSubstₙ : TypeSubstₙ → TypeSubstₙ
-- liftTypeSubstₙ f zero    = neu (var zero)
-- liftTypeSubstₙ f (suc x) = weakenTypeₙ (f x)

-- mutual
--   substTypeₙ : TypeSubstₙ → Typeₙ → Typeₙ
--   substTypeₙ f (neu τᵤ)    = substTypeᵤ f τᵤ
--   substTypeₙ f (fun τ₁ τ₂) = fun (substTypeₙ f τ₁) (substTypeₙ f τ₂)
--   substTypeₙ f (lam x τ)   = lam x (substTypeₙ (liftTypeSubstₙ f) τ)
--   substTypeₙ f (all x τ)   = all x (substTypeₙ (liftTypeSubstₙ f) τ)

--   substTypeᵤ : TypeSubstₙ → Typeᵤ → Typeₙ
--   substTypeᵤ f (var x)     = f x
--   substTypeᵤ f (app τ₁ τ₂) with substTypeᵤ f τ₁
--   ... | neu τᵤ    = neu (app τᵤ (substTypeₙ f τ₂))
--   ... | fun τ₁ τ₂ = {!   !}
--   ... | lam x τ   = substTypeAtZeroₙ (lam x τ) (substTypeₙ f τ₂)
--   ... | all x τ   = {!   !}

--   extendTypeSubstₙ : TypeSubstₙ → Typeₙ → TypeSubstₙ
--   extendTypeSubstₙ f τ zero    = τ
--   extendTypeSubstₙ f τ (suc x) = f x

--   substTypeAtZeroₙ : Typeₙ → Typeₙ → Typeₙ
--   substTypeAtZeroₙ τ τₛ = substTypeₙ (extendTypeSubstₙ (neu ∘ var) τₛ) τ

-- infix 5 _[_]ₙ
-- _[_]ₙ : Typeₙ → Typeₙ → Typeₙ
-- τ [ τₛ ]ₙ = substTypeAtZeroₙ τ τₛ

-- ⊨_ : Typeₙ → Typeₙ
-- ⊨ neu τᵤ = neu τᵤ
-- ⊨ fun τ₁ τ₂ = fun τ₁ τ₂
-- ⊨ all κ τ = all κ τ
-- ⊨ lam κ τ = neu (lam κ τ) ⊎ IndexRenaming → ⊨ κ → ⊨ κ'

-- data SemType : Set where
--   base : Typeᵤ → SemType
--   tfun : (IndexRenaming → SemType → SemType) → SemType

-- reifyTypeₙ : SemType → Typeₙ
-- reifyTypeₙ = {!   !}

-- reifyTypeᵤ : SemType → Typeᵤ
-- reifyTypeᵤ = {!   !}

-- _⊨_∶_ : KindCtx → SemType → Kind → Set
-- Δ ⊨ τₛ ∶ ⋆         = Δ ⊢ₙ reifyTypeₙ τₛ ∶ ⋆
-- Δ ⊨ τₛ ∶ tfun κ κ' = Δ ⊢ᵤ reifyTypeᵤ τₛ ∶ (tfun κ κ') ⊎ ∀ {Δ' f} → Renaming Δ Δ' f → Δ' ⊨ τₛ ∶ κ → Δ' ⊨ τₛ ∶ κ'
-- _⊨_ : KindCtx → Kind → Set
-- Δ ⊨ ⋆         = ∃[ τ ] Δ ⊢ₙ τ ∶ ⋆
-- Δ ⊨ tfun κ κ' = ∃[ τ ] Δ ⊢ᵤ τ ∶ tfun κ κ' ⊎ ∀ {Δ' f} → Renaming Δ Δ' f → Δ' ⊨ κ → Δ' ⊨ κ'

-- _⊨_∶_ : KindCtx → SemType → Kind → Set
-- Δ ⊨ base τᵤ ∶ ⋆         = Δ ⊢ᵤ τᵤ ∶ ⋆
-- Δ ⊨ tfun f τₛ ∶ tfun κ κ' = ∀ {Δ' f} → Renaming Δ Δ' f → Δ' ⊨ τₛ ∶ κ → Δ' ⊨ τₛ ∶ κ'


-- eval : ∀{Φ Ψ κ} → Ψ ⊢ κ → Env Ψ Φ → Φ ⊨ κ

--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

renameTyping : ∀ {Φ Ψ f} → Renaming Φ Ψ f → ∀ {τ κ} → Φ ⊢ τ ∶ κ → Ψ ⊢ renameType f τ ∶ κ
renameTyping ρ (var prf)       = var (ρ prf)
renameTyping ρ (fun prf₁ prf₂) = fun (renameTyping ρ prf₁) (renameTyping ρ prf₂)
renameTyping ρ (all prf)       = all (renameTyping (liftRenaming ρ) prf)
renameTyping ρ (lam prf)       = lam (renameTyping (liftRenaming ρ) prf)
renameTyping ρ (app prf₁ prf₂) = app (renameTyping ρ prf₁) (renameTyping ρ prf₂)

weakenTyping : ∀ {Φ κ κ' τ} → Φ ⊢ τ ∶ κ → κ' ∷ Φ ⊢ weakenType τ ∶ κ
weakenTyping prf = renameTyping there prf


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

extendTypingSubst : ∀ {Φ Ψ f} → TypingSubst Φ Ψ f → ∀ {κ τ} → Ψ ⊢ τ ∶ κ → TypingSubst (κ ∷ Φ) Ψ (extendTypeSubst f τ)
extendTypingSubst σ prf here        = prf
extendTypingSubst σ _   (there prf) = σ prf

substTypingHere : ∀ {Φ κ κ' τ τₛ} → κ ∷ Φ ⊢ τ ∶ κ' → Φ ⊢ τₛ ∶ κ → Φ ⊢ τ [ τₛ ] ∶ κ'
substTypingHere prf prfₛ = substTyping (extendTypingSubst var prfₛ) prf


--------------------------------------------------------------------------------
-- Proofs (normal)
--------------------------------------------------------------------------------

-- infix 1 _⟶w_

-- data _⟶w_ : (τ τ' : Type) → Set where
--   beta : ∀ {τ τₛ κ} → app (lam κ τ) τₛ ⟶w τ [ τₛ ]
--   appl : ∀ {τ τ' τₛ} → τ ⟶w τ' → app τ τₛ ⟶w app τ' τₛ

-- mutual
--   data WNe : Type → Set where
--     var : ∀ {x : Nat} → WNe (var x)
--     app : ∀ {τ₁ τ₂ : Type} → (wne : WNe τ₁) (wn : WN τ₂) → WNe (app τ₁ τ₂)

--   data WN : Type → Set where
--     neu : ∀ {τ} → WNe τ → WN τ
--     lam : ∀ {τ κ} → WN τ → WN (lam κ τ)
--     all : ∀ {τ κ} → WN τ → WN (all κ τ)
--     fun : ∀ {τ₁ τ₂} → WN τ₁ → WN τ₂ → WN (fun τ₁ τ₂)
--     exp : ∀ {τ τ'} → τ ⟶w τ' → WN τ' → WN τ

-- -- Red : (Γ : Context) (a : Ty) (t : Term Γ a) → Set
-- -- Red Γ (` α)   t = WN t
-- -- Red Γ (a ⇒ b) t = ∀{Δ} (ρ : Wk Δ Γ) {u : Term Δ a} (⟦u⟧ : Red Δ a u) → Red Δ b (app (wk ρ t) u)
-- _⊩_∶_ : KindCtx → Type → Kind → Set
-- Δ ⊩ τ ∶ ⋆         = WN τ
-- Δ ⊩ τ ∶ tfun κ κ' = ∀ {Δ' f} {ρ : Renaming Δ Δ' f} {τ' : Type} → Δ' ⊩ τ' ∶ κ → Δ' ⊩ app (renameType f τ) τ' ∶ κ'

-- normalization : Δ ⊢ τ ∶ κ → WN τ
-- normalization prf = {! subst WN (sub-id) (Red→WN (fund t ⟦idS⟧)) !}