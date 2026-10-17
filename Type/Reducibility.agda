{-# OPTIONS --allow-unsolved-metas #-}

module Type.Reducibility where

open import Prelude
open import Type
open import Type.Context
open import Type.Kinding
open import Type.Substitution
open import Type.Reduction
open import Type.Equality


--------------------------------------------------------------------------------
-- Syntax
--------------------------------------------------------------------------------

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

infix 3 _⊢ₙ_≡ₜ_∶_
data _⊢ₙ_≡ₜ_∶_ (Δ : KindCtx) : Type → Type → Kind → Set where
  -- TODO

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
    neu : Δ ⊩ᵤ τ ∶ κ → Δ ⊩ₙ τ ∶ κ
    fun : Δ ⊩ₙ τ ∶ ⋆ → Δ ⊩ₙ τ' ∶ ⋆ → Δ ⊩ₙ fun τ τ' ∶ ⋆
    all : κ ∷ Δ ⊩ₙ τ ∶ ⋆ → Δ ⊩ₙ all κ τ ∶ ⋆
    lam : κ ∷ Δ ⊩ₙ τ ∶ κ' → Δ ⊩ₙ lam κ τ ∶ tfun κ κ'
    exp : Δ ⊢ τ ⟶w τ' ∶ κ → Δ ⊩ₙ τ' ∶ κ → Δ ⊩ₙ τ ∶ κ

  infix 3 _⊩ᵤ_∶_
  data _⊩ᵤ_∶_ (Δ : KindCtx) : Type → Kind → Set where
    var : Δ ∋ x ↦ κ → Δ ⊩ᵤ var x ∶ κ
    app : Δ ⊩ᵤ τ ∶ tfun κ κ' → Δ ⊩ₙ τ' ∶ κ → Δ ⊩ᵤ app τ τ' ∶ κ'

-- Reducibility
infix 3 _⊩_∶_
_⊩_∶_ : KindCtx → Type → Kind → Set
Δ ⊩ τ ∶ ⋆         = Δ ⊩ₙ τ ∶ ⋆
Δ ⊩ τ ∶ tfun κ κ' = ∀ {Δ' f τ'} → Renaming Δ Δ' f → Δ' ⊩ τ' ∶ κ → Δ' ⊩ app (renameType f τ) τ' ∶ κ'

ReducibilitySubst : KindCtx → KindCtx → TypeSubst → Set
ReducibilitySubst Δ Δ' f = ∀ {x κ} → Δ ∋ x ↦ κ → Δ' ⊩ f x ∶ κ

-- "Validity" is reducibility under all reducible substitutions
Validity : KindCtx → Kind → Type → Set
Validity Δ κ τ = ∀{Δ' f} → ReducibilitySubst Δ Δ' f → Δ' ⊩ (substType f τ) ∶ κ

-- Validity' : KindCtx → Kind → Type → Set
-- Validity' Δ κ τ = Δ ⊩ τ ∶ κ

-- Fundamental theorem: Each well-typed term t is "valid"
validity : Δ ⊢ τ ∶ κ → Validity Δ κ τ
validity = {!   !}

wkW : Renaming Δ Δ' r → Δ ⊢ τ ⟶w τ' ∶ κ → Δ' ⊢ renameType r τ ⟶w renameType r τ' ∶ κ
wkW = {!   !}
-- wkW {ρ = ρ} (beta {t = t} {u = u}) =
--   subst
--     (app (abs (wk (keep ρ) t)) (wk ρ u) ⟶w_)
--     (wk-sg {t = t})  -- wk (keep ρ) t) [ wk ρ u ]₀  ≡ wk ρ (t [ u ]₀)
--     beta
-- wkW (appl w) = appl (wkW w)

mutual
  wk-WN : Renaming Δ Δ' r → Δ ⊩ₙ τ ∶ κ → Δ' ⊩ₙ renameType r τ ∶ κ
  wk-WN ρ (neu prf)       = neu (wk-WNe ρ prf)
  wk-WN ρ (fun prf₁ prf₂) = fun (wk-WN ρ prf₁) (wk-WN ρ prf₂)
  wk-WN ρ (all prf)       = all (wk-WN (liftRenaming ρ) prf)
  wk-WN ρ (lam prf)       = lam (wk-WN (liftRenaming ρ) prf)
  wk-WN ρ (exp prf₁ prf₂) = exp (wkW ρ prf₁) (wk-WN ρ prf₂)
  
  wk-WNe : Renaming Δ Δ' r → Δ ⊩ᵤ τ ∶ κ → Δ' ⊩ᵤ renameType r τ ∶ κ
  wk-WNe ρ (var prf)       = var (ρ prf)
  wk-WNe ρ (app prf₁ prf₂) = app (wk-WNe ρ prf₁) (wk-WN ρ prf₂)


-- Strengthening weak normalization

-- We need that WN (app t x) implies WN t if x does not appear in t.

-- First, we prove that if a weakened term weak-head reduces,
-- so does its original form.

-- wk-sg : {!   !}
-- wk-sg = {!   !}

-- whd-strengthen : κ' ∷ Δ ⊢ weakenType τ₁ ⟶w τ₂ ∶ κ → ∃[ τ₂' ] (Δ ⊢ τ₁ ⟶w τ₂' ∶ κ) × (weakenType τ₂' ≡ τ₂)
-- whd-strengthen = {!   !}
-- whd-strengthen {τ₁ = app (var x) τₛ} (appl ())
-- whd-strengthen {τ₁ = app (lam κ τ) τₛ} (beta _ _) = ⟨ τ [ τₛ ] , ⟨ beta ? ? , sym wk-sg ⟩ ⟩
--   -- Need:  wk ρ (t [ u ]₀) ≡ wk (keep ρ) t [ wk ρ u ]₀
-- whd-strengthen {t = app (app t u₁) u₂} (appl r) with whd-strengthen r
-- ... | ⟨ _ , ⟨ r' , refl ⟩ ⟩ = ⟨ _ , ⟨ appl r' , refl ⟩ ⟩

-- idx-strengthen : κ' ∷ Δ ∋ suc x ↦ κ → Δ ∋ x ↦ κ
-- idx-strengthen (there prf) = prf

-- type-strengthen : renameType r τ → τ
-- type-strengthen {τ = var x} 

-- liftStrengthening : ∀ {κ''} → (κ' ∷ Δ ⊩ₙ (weakenType τ) ∶ κ → Δ ⊩ₙ τ ∶ κ) → κ'' ∷ κ' ∷ Δ ⊩ₙ (renameType (liftIndexRenaming suc) τ) ∶ κ → κ'' ∷ Δ ⊩ₙ τ ∶ κ
-- liftStrengthening {τ = var x}     s (neu prf) = neu (liftStrengthening prf)
-- liftStrengthening {τ = app τ₁ τ₂} s (neu prf) = neu (liftStrengthening prf)
-- liftStrengthening {τ = lam κ τ}   s (lam prf) = lam (liftStrengthening liftStrengthening prf)
-- liftStrengthening (exp prf₁ prf₂) s with whd-strengthen prf₁
-- ... | ⟨ _ , ⟨ prf₁' , refl ⟩ ⟩ = exp prf₁' (liftStrengthening prf₂)

-- mutual
--   WN-strengthen-lifted : ∀ {κ''} → κ'' ∷ κ' ∷ Δ ⊩ₙ renameType (liftIndexRenaming suc) τ ∶ κ → κ'' ∷ Δ ⊩ₙ τ ∶ κ
--   WN-strengthen-lifted {τ = var x}     (neu prf) = neu (WNe-strengthen-lifted prf)
--   WN-strengthen-lifted {τ = app τ₁ τ₂} (neu prf) = neu (WNe-strengthen-lifted prf)
--   WN-strengthen-lifted {τ = lam κ τ}   (lam prf) = lam (WN-strengthen-lifted {! prf !})
--   -- WN-strengthen-lifted (exp prf₁ prf₂) with whd-strengthen prf₁
--   -- ... | ⟨ _ , ⟨ prf₁' , refl ⟩ ⟩ = exp prf₁' (WN-strengthen prf₂)

--   WNe-strengthen-lifted : ∀ {κ''} → κ'' ∷ κ' ∷ Δ ⊩ᵤ renameType (liftIndexRenaming suc) τ ∶ κ → κ'' ∷ Δ ⊩ᵤ τ ∶ κ
--   WNe-strengthen-lifted = {!   !}

-- mutual
--   WN-strengthen : {Renaming Δ Δ' r} → Δ' ⊩ₙ renameType r τ ∶ κ → Δ ⊩ₙ τ ∶ κ
--   WN-strengthen {τ = lam κ τ}   (lam prf) = lam (WN-strengthen prf)
--   WN-strengthen (neu prf) = neu (WNe-strengthen prf)
--   -- WN-strengthen {τ = app τ₁ τ₂} (neu prf) = neu (WNe-strengthen prf)
--   WN-strengthen (exp prf₁ prf₂) with whd-strengthen prf₁
--   ... | ⟨ _ , ⟨ prf₁' , refl ⟩ ⟩ = exp prf₁' (WN-strengthen prf₂)

--   -- WNe-strengthen : Renaming Δ (κ' ∷ Δ) f → κ' ∷ Δ ⊩ᵤ (renameType f τ) ∶ κ → Δ ⊩ᵤ τ ∶ κ
--   WNe-strengthen : κ' ∷ Δ ⊩ᵤ weakenType τ ∶ κ → Δ ⊩ᵤ τ ∶ κ
--   WNe-strengthen {τ = var x}     (var prf) = var (idx-strengthen prf)
--   WNe-strengthen {τ = app τ₁ τ₂} (app prf₁ prf₂) = app (WNe-strengthen prf₁) (WN-strengthen prf₂)


-- Eta contraction
-- The renaming ⇑↑ : Γ.a.a ≤ Γ.a has an inverse,
-- the substitution id.0 : Γ.a ⊢ Γ.a.a,
-- so we have (⇑↑ t)[id.0] ≡ t.
-- contraction-after-weakening : Δ ⊢ renameType (liftIndexRenaming suc) τ [ var zero ] ≡ₜ τ ∶ κ
-- contraction-after-weakening = {!   !}
-- contraction-after-weakening {t = t} = begin
--   wk (keep (skip idW)) t [ var zero ]₀                        ≡⟨ sub-wk {σ = idS ∙ var zero} {t = t} ⟩
--   sub (compSW (idS ∙ var zero) (keep (skip idW)))           t ≡⟨⟩                                               -- lem0 begin
--   sub (compSW idS                   (skip idW) ∙ var zero)  t ≡⟨⟩
--   sub (compSW (weak idS ∙ var zero) (skip idW) ∙ var zero)  t ≡⟨⟩
--   sub (compSW (weak idS)            idW        ∙ var zero)  t ≡⟨⟩
--   sub (compSW (weak idS ∙ var zero) (keep idW))             t ≡⟨⟩
--   sub (compSW idS idW)                                      t ≡⟨ cong (λ σ → sub σ t) (comp-S-idW {ρ = idW}) ⟩  -- lem0 end
--   sub idS                                                   t ≡⟨ sub-id ⟩
--   t ∎ where open ≡-Reasoning

-- invertHere : κ' ∷ Δ ∋ zero ↦ κ → κ ≡ κ'
-- invertHere here = refl

postulate WN-η-contract : κ' ∷ Δ ⊩ₙ app (weakenType τ) (var zero) ∶ κ₂ → Δ ⊩ₙ τ ∶ tfun κ' κ₂
-- WN-η-contract                 (neu (app prf₁ (neu (var prf₂)))) rewrite invertHere prf₂ = neu (WNe-strengthen prf₁)
-- WN-η-contract {τ = var x}     (exp (appl ()) _)
-- -- WN-η-contract {τ = lam κ τ}   (exp (beta _ _) prf) = lam (subst _ contraction-after-weakening prf)
-- -- WN-η-contract {τ = app τ₁ τ₂} (exp (appl prf₁) prf₂) with whd-strengthen prf₁
-- -- ... | ⟨ _ , ⟨ prf₁' , refl ⟩ ⟩ = exp prf₁' (WN-η-contract prf₂)

mutual
  -- This is the equivalent to reification.
  Red→WN : Δ ⊩ τ ∶ κ → Δ ⊩ₙ τ ∶ κ
  Red→WN {κ = ⋆}         prf = prf
  Red→WN {κ = tfun κ κ'} ⟦t⟧ = WN-η-contract (Red→WN (⟦t⟧ there ⟦var0⟧))

  -- This is the equivalent to reflection.
  WNe→Red : Δ ⊩ᵤ τ ∶ κ → Δ ⊩ τ ∶ κ
  WNe→Red {κ = ⋆}         prf      = neu prf
  WNe→Red {κ = tfun κ κ'} ⟦t⟧ ρ ⟦u⟧ = WNe→Red (app (wk-WNe ρ ⟦t⟧) (Red→WN ⟦u⟧))

  -- Reflection of the 0th variable.
  ⟦var0⟧ : κ ∷ Δ ⊩ var zero ∶ κ
  ⟦var0⟧ = WNe→Red (var here)

renameReducibilityₙ : ∀ {Δ Δ' f} → Renaming Δ Δ' f → ∀ {τ κ} → Δ ⊩ₙ τ ∶ κ → Δ' ⊩ₙ renameType f τ ∶ κ
renameReducibilityₙ = {!   !}

renameReducibility : ∀ {Δ Δ' f τ κ} → Renaming Δ Δ' f → Δ ⊩ τ ∶ κ → Δ' ⊩ renameType f τ ∶ κ
renameReducibility {κ = ⋆}         ρ prf = renameReducibilityₙ ρ prf
renameReducibility {κ = tfun κ κ'} ρ prf = {!   !}
-- renameReducibility {κ = ⋆} ρ (var prf)       = var (ρ prf)
-- renameReducibility ρ (fun prf₁ prf₂) = fun (renameReducibility ρ prf₁) (renameReducibility ρ prf₂)
-- renameReducibility ρ (all prf)       = all (renameReducibility (liftRenaming ρ) prf)
-- renameReducibility ρ (lam prf)       = lam (renameReducibility (liftRenaming ρ) prf)
-- renameReducibility ρ (app prf₁ prf₂) = app (renameReducibility ρ prf₁) (renameReducibility ρ prf₂)

weakenReducibility : ∀ {Δ κ κ' τ} → Δ ⊩ τ ∶ κ → κ' ∷ Δ ⊩ weakenType τ ∶ κ
weakenReducibility = renameReducibility there

liftReducibilitySubst : ∀ {Φ Ψ f} → ReducibilitySubst Φ Ψ f → ∀ {κ} → ReducibilitySubst (κ ∷ Φ) (κ ∷ Ψ) (liftTypeSubst f)
liftReducibilitySubst σ here        = ⟦var0⟧
liftReducibilitySubst σ (there prf) = weakenReducibility (σ prf)

-- extendReducibilitySubst : ∀ {Δ Δ' f} → ReducibilitySubst Δ Δ' f → ∀ {κ τ} → Δ' ⊩ τ ∶ κ → ReducibilitySubst (κ ∷ Δ) Δ' (extendTypeSubst f τ)
-- extendReducibilitySubst σ prf here        = prf
-- extendReducibilitySubst σ _   (there prf) = σ prf


liftTypeSubst-id : liftTypeSubst var x ≡ var x
liftTypeSubst-id {zero}  = refl
liftTypeSubst-id {suc x} = refl

substType-liftTypeSubst-id : substType (liftTypeSubst var) τ ≡ τ
substType-liftTypeSubst-id {var x}     = liftTypeSubst-id
substType-liftTypeSubst-id {fun τ₁ τ₂} = cong₂ fun substType-liftTypeSubst-id substType-liftTypeSubst-id
substType-liftTypeSubst-id {lam x τ}   = subst _ liftTypeSubst-id (cong (lam x) substType-liftTypeSubst-id)
substType-liftTypeSubst-id {app τ₁ τ₂} = cong₂ app substType-liftTypeSubst-id substType-liftTypeSubst-id
substType-liftTypeSubst-id {all x τ}   = subst _ liftTypeSubst-id (cong (lam x) substType-liftTypeSubst-id)

substType-id : substType var τ ≡ τ
substType-id {var x}     = refl
substType-id {fun τ₁ τ₂} = cong₂ fun substType-id substType-id
substType-id {lam κ τ}   = cong (lam κ) substType-liftTypeSubst-id
substType-id {app τ₁ τ₂} = cong₂ app substType-id substType-id
substType-id {all κ τ}   = cong (all κ) substType-liftTypeSubst-id


-- The identity substitution is reducible
idSubst : ReducibilitySubst Δ Δ var
idSubst {κ ∷ Δ} = subst _ liftTypeSubst-id (liftReducibilitySubst idSubst)

normalization : Δ ⊢ τ ∶ κ → Δ ⊩ₙ τ ∶ κ
normalization p = subst _ substType-id (Red→WN (validity p idSubst))