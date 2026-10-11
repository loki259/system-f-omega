{-# OPTIONS --allow-unsolved-metas #-}

module TypeNormalization where

open import Prelude
open import Syntax
open import Context
open import Kinding


-- infix 3 _⟶w_
infix 3 _⊢_⟶w_∶_

postulate
  -- _⟶w_ : Type → Type → Set
  _⊢_⟶w_∶_ : (Δ : KindCtx) → Type → Type → Kind → Set

--------------------------------------------------------------------------------
-- Syntax
--------------------------------------------------------------------------------

-- mutual
--   data Typeₙ : Set where
--     neu : Typeᵤ → Typeₙ
--     fun : Typeₙ → Typeₙ → Typeₙ
--     all : Kind → Typeₙ → Typeₙ
--     lam : Kind → Typeₙ → Typeₙ

--   data Typeᵤ : Set where
--     var : Index → Typeᵤ
--     app : Typeᵤ → Typeₙ → Typeᵤ

mutual
  data Normal : Type → Set where
    neu : Neutral τ → Normal τ
    fun : Normal τ₁ → Normal τ₂ → Normal (fun τ₁ τ₂)
    all : (κ : Kind) → Normal τ  → Normal (all κ τ)
    lam : (κ : Kind) → Normal τ  → Normal (lam κ τ)

  data Neutral : Type → Set where
    var : (x : Index) → Neutral (var x)
    app : Neutral τ₁ → Normal τ₂ → Neutral (app τ₁ τ₂)

variable
  τₙ τₙ' τₙ₁ τₙ₁' τₙ₂ τₙ₂' : ∀ {τ} → Normal τ
  τᵤ τᵤ' τᵤ₁ τᵤ₁' τᵤ₂ τᵤ₂' : ∀ {τ} → Neutral τ

-- mutual
--   data Normalizing : Type → Set where
--     neu : Neutralizing τ → Normalizing τ
--     fun : Normalizing τ₁ → Normalizing τ₂ → Normalizing (fun τ₁ τ₂)
--     all : (κ : Kind) → Normalizing τ  → Normalizing (all κ τ)
--     lam : (κ : Kind) → Normalizing τ → Normalizing (lam κ τ)
--     exp : τ ⟶w τ' → Normalizing τ' → Normalizing τ
  
--   data Neutralizing : Type → Set where
--     var : (x : Index) → Neutralizing (var x)
--     app : Neutralizing τ₁ → Normalizing τ₂ → Neutralizing (app τ₁ τ₂)


--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------
    
-- mutual
--   infix 3 _⊢ₙ_∶_
--   data _⊢ₙ_∶_ (Δ : KindCtx) : Typeₙ → Kind → Set where
--     neu : ∀ {τ} → Δ ⊢ᵤ τ ∶ ⋆ → Δ ⊢ₙ neu τ ∶ ⋆
--     fun : ∀ {τ τ'} → Δ ⊢ₙ τ ∶ ⋆ → Δ ⊢ₙ τ' ∶ ⋆ → Δ ⊢ₙ fun τ τ' ∶ ⋆
--     all : ∀ {κ τ} → κ ∷ Δ ⊢ₙ τ ∶ ⋆ → Δ ⊢ₙ all κ τ ∶ ⋆
--     lam : ∀ {κ κ' τ} → κ ∷ Δ ⊢ₙ τ ∶ κ' → Δ ⊢ₙ lam κ τ ∶ tfun κ κ'

--   infix 3 _⊢ᵤ_∶_
--   data _⊢ᵤ_∶_ (Δ : KindCtx) : Typeᵤ → Kind → Set where
--     var : ∀ {x} → Δ ∋ x ↦ κ → Δ ⊢ᵤ var x ∶ κ
--     app : ∀ {τ τ' κ κ'} → Δ ⊢ᵤ τ ∶ tfun κ κ' → Δ ⊢ₙ τ' ∶ κ → Δ ⊢ᵤ app τ τ' ∶ κ'

mutual
  infix 3 _⊢ₙ_∶_
  data _⊢ₙ_∶_ (Δ : KindCtx) : ∀ {τ} → Normal τ → Kind → Set where
    neu : Δ ⊢ᵤ (τᵤ {τ}) ∶ ⋆ → Δ ⊢ₙ neu (τᵤ {τ}) ∶ ⋆
    fun : Δ ⊢ₙ (τₙ {τ}) ∶ ⋆ → Δ ⊢ₙ (τₙ' {τ}) ∶ ⋆ → Δ ⊢ₙ fun (τₙ {τ}) (τₙ' {τ}) ∶ ⋆
    all : κ ∷ Δ ⊢ₙ (τₙ {τ}) ∶ ⋆ → Δ ⊢ₙ all κ (τₙ {τ}) ∶ ⋆
    lam : κ ∷ Δ ⊢ₙ (τₙ {τ}) ∶ κ' → Δ ⊢ₙ lam κ (τₙ {τ}) ∶ tfun κ κ'

  infix 3 _⊢ᵤ_∶_
  data _⊢ᵤ_∶_ (Δ : KindCtx) : ∀ {τ} → Neutral τ → Kind → Set where
    var : Δ ∋ x ↦ κ → Δ ⊢ᵤ var x ∶ κ
    app : Δ ⊢ᵤ (τᵤ {τ}) ∶ tfun κ κ' → Δ ⊢ₙ (τₙ {τ}) ∶ κ → Δ ⊢ᵤ app (τᵤ {τ}) (τₙ {τ}) ∶ κ'

mutual
  infix 3 _⊩ₙ_∶_
  data _⊩ₙ_∶_ (Δ : KindCtx) : Type → Kind → Set where
    neu : Δ ⊩ᵤ τ ∶ ⋆ → Δ ⊩ₙ τ ∶ ⋆
    fun : Δ ⊩ₙ τ ∶ ⋆ → Δ ⊩ₙ τ' ∶ ⋆ → Δ ⊩ₙ fun τ τ' ∶ ⋆
    all : κ ∷ Δ ⊩ₙ τ ∶ ⋆ → Δ ⊩ₙ all κ τ ∶ ⋆
    lam : κ ∷ Δ ⊩ₙ τ ∶ κ' → Δ ⊩ₙ lam κ τ ∶ tfun κ κ'
    exp : Δ ⊢ τ ⟶w τ' ∶ κ → Δ ⊩ₙ τ' ∶ κ → Δ ⊩ₙ τ ∶ κ

  infix 3 _⊩ᵤ_∶_
  data _⊩ᵤ_∶_ (Δ : KindCtx) : Type → Kind → Set where
    var : Δ ∋ x ↦ κ → Δ ⊩ᵤ var x ∶ κ
    app : Δ ⊩ᵤ τ ∶ tfun κ κ' → Δ ⊩ₙ τ' ∶ κ → Δ ⊩ᵤ app τ τ' ∶ κ'

-- Red : (Γ : Context) (a : Ty) (t : Term Γ a) → Set
-- Red Γ (` α)   t = WN t
-- Red Γ (a ⇒ b) t = ∀{Δ} (ρ : Wk Δ Γ) {u : Term Δ a} (⟦u⟧ : Red Δ a u) → Red Δ b (app (wk ρ t) u)
-- _⊩_∶_ : KindCtx → Type → Kind → Set
-- Δ ⊩ τ ∶ ⋆         = Δ ⊩ₙ τ ∶ ⋆
-- Δ ⊩ τ ∶ tfun κ κ' = ∀ {Δ' f τ'} → Renaming Δ Δ' f → Δ' ⊩ τ' ∶ κ → Δ' ⊩ app (renameType f τ) τ' ∶ κ'


-- mutual
  -- renameTypeₙ : ∀ {Φ Ψ} → Renaming Φ Ψ → ∀ {τ κ} → Φ ⊢ₙ τ ∶ κ → ∃[ τ' ] Ψ ⊢ₙ τ' ∶ κ
  -- renameTypeₙ ρ (neu u)         = Σ-map₂ neu (renameTypeᵤ ρ u)
  -- renameTypeₙ ρ (lam prf)       = Σ-map (lam _) lam (renameTypeₙ (lift ρ) prf)
  -- renameTypeₙ ρ (fun prf₁ prf₂) = Σ-zip fun fun (renameTypeₙ ρ prf₁) (renameTypeₙ ρ prf₂)
  -- renameTypeₙ ρ (all prf)       = Σ-map (all _) all (renameTypeₙ (lift ρ) prf)

  -- renameTypeᵤ : ∀ {Φ Ψ} → Renaming Φ Ψ → ∀ {τ κ} → Φ ⊢ᵤ τ ∶ κ → ∃[ τ' ] Ψ ⊢ᵤ τ' ∶ κ
  -- renameTypeᵤ ρ (var prf)       = Σ-map var var (ρ prf)
  -- renameTypeᵤ ρ (app prf₁ prf₂) = Σ-zip app app (renameTypeᵤ ρ prf₁) (renameTypeₙ ρ prf₂)

-- weakenTypeₙ : ∀ {Φ κ κ' τ} → Φ ⊢ₙ τ ∶ κ → ∃[ τ' ] κ' ∷ Φ ⊢ₙ τ' ∶ κ
-- weakenTypeₙ = renameTypeₙ λ prf → -, there prf
