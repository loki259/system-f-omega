{-# OPTIONS --allow-unsolved-metas #-}

module Type.Substitution where

open import Prelude
open import Type
open import Type.Context
open import Type.Kinding


--------------------------------------------------------------------------------
-- Syntax
--------------------------------------------------------------------------------

renameType : IndexRenaming → Type → Type
renameType r (var x)     = var (r x)
renameType r (fun τ₁ τ₂) = fun (renameType r τ₁) (renameType r τ₂)
renameType r (lam κ τ)   = lam κ (renameType (liftIndexRenaming r) τ)
renameType r (app τ₁ τ₂) = app (renameType r τ₁) (renameType r τ₂)
renameType r (all κ τ)   = all κ (renameType (liftIndexRenaming r) τ)

lifted-IndexRenaming-∘ : liftIndexRenamingN n r' (liftIndexRenamingN n r x) ≡ liftIndexRenamingN n (r' ∘ r) x
lifted-IndexRenaming-∘ {n = zero}              = refl
lifted-IndexRenaming-∘ {n = suc n} {x = zero}  = refl
lifted-IndexRenaming-∘ {n = suc n} {x = suc x} = cong suc (lifted-IndexRenaming-∘ {n = n})

lifted-renameType-∘ : renameType (liftIndexRenamingN n r') (renameType (liftIndexRenamingN n r) τ) ≡ renameType (liftIndexRenamingN n (r' ∘ r)) τ
lifted-renameType-∘ {n = n} {τ = var x}     = cong var (lifted-IndexRenaming-∘ {n = n})
lifted-renameType-∘ {n = n} {τ = fun τ₁ τ₂} = cong₂ fun (lifted-renameType-∘ {n = n}) (lifted-renameType-∘ {n = n})
lifted-renameType-∘ {n = n} {τ = app τ₁ τ₂} = cong₂ app (lifted-renameType-∘ {n = n}) (lifted-renameType-∘ {n = n})
lifted-renameType-∘ {n = n} {r' = r'} {r = r} {τ = lam κ τ}
  rewrite lemma-contract-liftIndexRenaming {n = n} {r = r'}
  rewrite lemma-contract-liftIndexRenaming {n = n} {r = r}
  rewrite lemma-contract-liftIndexRenaming {n = n} {r = r' ∘ r}
  = cong (lam κ) (lifted-renameType-∘ {n = suc n})
lifted-renameType-∘ {n = n} {r' = r'} {r = r} {τ = all κ τ}
  rewrite lemma-contract-liftIndexRenaming {n = n} {r = r'}
  rewrite lemma-contract-liftIndexRenaming {n = n} {r = r}
  rewrite lemma-contract-liftIndexRenaming {n = n} {r = r' ∘ r}
  = cong (all κ) (lifted-renameType-∘ {n = suc n})

renameType-∘ : renameType r' (renameType r τ) ≡ renameType (r' ∘ r) τ
renameType-∘ = lifted-renameType-∘ {n = zero}

-- renameType-∘ : renameType r' (renameType r τ) ≡ renameType (r' ∘ r) τ
-- renameType-∘ {τ = var x}     = refl
-- renameType-∘ {τ = fun τ₁ τ₂} = cong₂ fun renameType-∘ renameType-∘
-- -- renameType-∘ {τ = lam κ τ}   = cong (lam κ) (trans renameType-∘ (cong (λ x → renameType x τ) (function-extensionality liftIndexRenaming-∘)))
-- renameType-∘ {τ = lam κ τ}   = cong (lam κ) {!   !} -- (trans renameType-∘ (cong (λ x → renameType x τ) (function-extensionality liftIndexRenaming-∘)))
-- renameType-∘ {τ = app τ₁ τ₂} = cong₂ app renameType-∘ renameType-∘
-- renameType-∘ {τ = all κ τ}   = cong (all κ) (trans renameType-∘ (cong (λ x → renameType x τ) (function-extensionality liftIndexRenaming-∘)))

weakenType : Type → Type
weakenType = renameType suc


TypeSubst : Set
TypeSubst = Index → Type

variable
  s s' : TypeSubst

liftTypeSubstN : (n : Nat) → TypeSubst → TypeSubst
liftTypeSubstN 0       s         = s
liftTypeSubstN (suc _) s 0       = var 0
liftTypeSubstN (suc n) s (suc x) = weakenType (liftTypeSubstN n s x)

liftTypeSubst : TypeSubst → TypeSubst
liftTypeSubst = liftTypeSubstN 1

lemma-contract-liftTypeSubst : liftTypeSubstN 1 (liftTypeSubstN n s) ≡ liftTypeSubstN (suc n) s
lemma-contract-liftTypeSubst {n = 0}     = refl
lemma-contract-liftTypeSubst {n = suc n} = function-extensionality λ { {0}  → refl; {suc n} → refl }

substType : TypeSubst → Type → Type
substType s (var x)     = s x
substType s (fun τ₁ τ₂) = fun (substType s τ₁) (substType s τ₂)
substType s (lam κ τ)   = lam κ (substType (liftTypeSubst s) τ)
substType s (app τ₁ τ₂) = app (substType s τ₁) (substType s τ₂)
substType s (all κ τ)   = all κ (substType (liftTypeSubst s) τ)

extendTypeSubst : TypeSubst → Type → TypeSubst
extendTypeSubst s τ 0       = τ
extendTypeSubst s τ (suc x) = s x

substTypeAtZero : Type → Type → Type
substTypeAtZero τ τₛ = substType (extendTypeSubst var τₛ) τ

infix 5 _[_]
_[_] : Type → Type → Type
τ [ τₛ ] = substTypeAtZero τ τₛ


--------------------------------------------------------------------------------
-- Syntax (normal)
--------------------------------------------------------------------------------

-- mutual
--   renameTypeₙ : IndexRenaming → Typeₙ → Typeₙ
--   renameTypeₙ f (neu τᵤ)    = neu (renameTypeᵤ f τᵤ)
--   renameTypeₙ f (fun τ₁ τ₂) = fun (renameTypeₙ f τ₁) (renameTypeₙ f τ₂)
--   renameTypeₙ f (lam x τ)   = lam x (renameTypeₙ (liftIndexRenaming f) τ)
--   renameTypeₙ f (all x τ)   = all x (renameTypeₙ (liftIndexRenaming f) τ)

--   renameTypeᵤ : IndexRenaming → Typeᵤ → Typeᵤ
--   renameTypeᵤ f (var x)     = var (f x)
--   renameTypeᵤ f (app τ₁ τ₂) = app (renameTypeᵤ f τ₁) (renameTypeₙ f τ₂)

-- weakenTypeₙ : Typeₙ → Typeₙ
-- weakenTypeₙ τ = renameTypeₙ suc τ


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

renameKinding : ∀ {Φ Ψ f} → Renaming Φ Ψ f → ∀ {τ κ} → Φ ⊢ τ ∶ κ → Ψ ⊢ renameType f τ ∶ κ
renameKinding ρ (var prf)       = var (ρ prf)
renameKinding ρ (fun prf₁ prf₂) = fun (renameKinding ρ prf₁) (renameKinding ρ prf₂)
renameKinding ρ (all prf)       = all (renameKinding (liftRenaming ρ) prf)
renameKinding ρ (lam prf)       = lam (renameKinding (liftRenaming ρ) prf)
renameKinding ρ (app prf₁ prf₂) = app (renameKinding ρ prf₁) (renameKinding ρ prf₂)

weakenKinding : ∀ {Φ κ κ' τ} → Φ ⊢ τ ∶ κ → κ' ∷ Φ ⊢ weakenType τ ∶ κ
weakenKinding = renameKinding there


KindingSubst : KindCtx → KindCtx → TypeSubst → Set
KindingSubst Φ Ψ f = ∀ {x κ} → Φ ∋ x ↦ κ → Ψ ⊢ f x ∶ κ

liftKindingSubst : ∀ {Φ Ψ f} → KindingSubst Φ Ψ f → ∀ {κ} → KindingSubst (κ ∷ Φ) (κ ∷ Ψ) (liftTypeSubst f)
liftKindingSubst σ here        = var here
liftKindingSubst σ (there prf) = weakenKinding (σ prf)

substKinding : ∀ {Φ Ψ f} → KindingSubst Φ Ψ f → ∀ {κ τ} → Φ ⊢ τ ∶ κ → Ψ ⊢ substType f τ ∶ κ
substKinding σ (var prf)       = σ prf
substKinding σ (lam prf)       = lam (substKinding (liftKindingSubst σ) prf)
substKinding σ (app prf₁ prf₂) = app (substKinding σ prf₁) (substKinding σ prf₂)
substKinding σ (fun prf₁ prf₂) = fun (substKinding σ prf₁) (substKinding σ prf₂)
substKinding σ (all prf)       = all (substKinding (liftKindingSubst σ) prf)

extendKindingSubst : ∀ {Φ Ψ f} → KindingSubst Φ Ψ f → ∀ {κ τ} → Ψ ⊢ τ ∶ κ → KindingSubst (κ ∷ Φ) Ψ (extendTypeSubst f τ)
extendKindingSubst σ prf here        = prf
extendKindingSubst σ _   (there prf) = σ prf

substKindingHere : ∀ {Φ κ κ' τ τₛ} → κ ∷ Φ ⊢ τ ∶ κ' → Φ ⊢ τₛ ∶ κ → Φ ⊢ τ [ τₛ ] ∶ κ'
substKindingHere prf prfₛ = substKinding (extendKindingSubst var prfₛ) prf


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


--------------------------------------------------------------------------------

-- FIXME: move to Context?
idRenaming : Renaming Δ Δ id
idRenaming = id

-- FIXME: move to Context?
liftIndexRenaming-id : liftIndexRenamingN n id x ≡ x
liftIndexRenaming-id {n = 0}                 = refl
liftIndexRenaming-id {n = suc n} {x = 0}     = refl
liftIndexRenaming-id {n = suc n} {x = suc x} = cong suc (liftIndexRenaming-id {n = n})

lifted-renameType-idRenaming-id : renameType (liftIndexRenamingN n id) τ ≡ τ
lifted-renameType-idRenaming-id {n = n} {var x}
  = cong var (liftIndexRenaming-id {n = n})
lifted-renameType-idRenaming-id {n = n} {fun τ₁ τ₂}
  = cong₂ fun (lifted-renameType-idRenaming-id {n = n}) (lifted-renameType-idRenaming-id {n = n})
lifted-renameType-idRenaming-id {n = n} {app τ₁ τ₂}
  = cong₂ app (lifted-renameType-idRenaming-id {n = n}) (lifted-renameType-idRenaming-id {n = n})
lifted-renameType-idRenaming-id {n = n} {lam κ τ}
  rewrite lemma-contract-liftIndexRenaming {n = n} {r = id}
  = cong (lam κ) (lifted-renameType-idRenaming-id {n = suc n})
lifted-renameType-idRenaming-id {n = n} {all κ τ}
  rewrite lemma-contract-liftIndexRenaming {n = n} {r = id}
  = cong (all κ) (lifted-renameType-idRenaming-id {n = suc n})

renameType-idRenaming-id : renameType id τ ≡ τ
renameType-idRenaming-id = lifted-renameType-idRenaming-id {n = 0}



liftTypeSubst-id : liftTypeSubstN n var x ≡ var x
liftTypeSubst-id {n = 0}            = refl
liftTypeSubst-id {n = suc _} {zero} = refl
liftTypeSubst-id {n = suc n} {suc x} rewrite liftTypeSubst-id {n = n} {x = x} = refl

lifted-substType-id : substType (liftTypeSubstN n var) τ ≡ τ
lifted-substType-id {n = n} {var x}     = liftTypeSubst-id {n = n}
lifted-substType-id {n = n} {fun τ₁ τ₂} = cong₂ fun (lifted-substType-id {n = n}) (lifted-substType-id {n = n})
lifted-substType-id {n = n} {app τ₁ τ₂} = cong₂ app (lifted-substType-id {n = n}) (lifted-substType-id {n = n})
lifted-substType-id {n = n} {lam κ τ} rewrite lemma-contract-liftTypeSubst {n = n} {s = var}
  = cong (lam κ) (lifted-substType-id {n = suc n})
lifted-substType-id {n = n} {all κ τ} rewrite lemma-contract-liftTypeSubst {n = n} {s = var}
  = cong (all κ) (lifted-substType-id {n = suc n})

substType-id : substType var τ ≡ τ
substType-id = lifted-substType-id {n = 0}



lifted-lemma-substTypeAtZero-suc : liftTypeSubstN n (extendTypeSubst var τₛ) (liftIndexRenamingN n suc x) ≡ var x
lifted-lemma-substTypeAtZero-suc {n = 0}                 = refl
lifted-lemma-substTypeAtZero-suc {n = suc n} {x = 0}     = refl
lifted-lemma-substTypeAtZero-suc {n = suc n} {x = suc x} = cong weakenType (lifted-lemma-substTypeAtZero-suc {n = n})

lifted-lemma-substTypeAtZero-weakened : substType (liftTypeSubstN n (extendTypeSubst var τₛ)) (renameType (liftIndexRenamingN n suc) τ) ≡ τ
lifted-lemma-substTypeAtZero-weakened {n = n} {τ = var x}     = lifted-lemma-substTypeAtZero-suc {n = n}
lifted-lemma-substTypeAtZero-weakened {n = n} {τ = fun τ₁ τ₂} = cong₂ fun lifted-lemma-substTypeAtZero-weakened lifted-lemma-substTypeAtZero-weakened
lifted-lemma-substTypeAtZero-weakened {n = n} {τ = app τ₁ τ₂} = cong₂ app lifted-lemma-substTypeAtZero-weakened lifted-lemma-substTypeAtZero-weakened
lifted-lemma-substTypeAtZero-weakened {n = n} {τₛ = τₛ} {τ = lam κ τ}
  rewrite lemma-contract-liftTypeSubst {n = n} {s = extendTypeSubst var τₛ}
  rewrite lemma-contract-liftIndexRenaming {n = n} {r = suc}
  = cong (lam κ) (lifted-lemma-substTypeAtZero-weakened {n = suc n})
lifted-lemma-substTypeAtZero-weakened {n = n} {τₛ = τₛ} {τ = all κ τ}
  rewrite lemma-contract-liftTypeSubst {n = n} {s = extendTypeSubst var τₛ}
  rewrite lemma-contract-liftIndexRenaming {n = n} {r = suc}
  = cong (all κ) (lifted-lemma-substTypeAtZero-weakened {n = suc n})

lemma-substTypeAtZero-weakened : substTypeAtZero (weakenType τ) τₛ ≡ τ
lemma-substTypeAtZero-weakened = lifted-lemma-substTypeAtZero-weakened {n = 0}

-- lemma-rename-weakened : renameType (liftIndexRenaming r) (weakenType τ) ≡ weakenType (renameType r τ)
-- lemma-rename-weakened {r = r} {τ = τ}
--   rewrite renameType-∘ {r' = liftIndexRenaming r} {r = suc} {τ = τ}
--   rewrite renameType-∘ {r' = suc} {r = r} {τ = τ} = refl

-- lemma-strengthen-subst : renameType r (s x) ≡ substType (extendTypeSubst var τₛ) (renameType (liftIndexRenaming r) (weakenType (s x)))
-- lemma-strengthen-subst {x = zero} = {!   !}
-- lemma-strengthen-subst {x = suc x} = {!   !}

-- lifted-lemma-mon : substType (liftTypeSubstN n (extendTypeSubst (λ x → renameType r (s x)) τₛ)) τ ≡ substType (liftTypeSubstN n (extendTypeSubst var τₛ)) (renameType (liftIndexRenamingN n (liftIndexRenaming r)) (substType (liftTypeSubstN n (liftTypeSubst s)) τ))
-- lifted-lemma-mon {n = 0} {τ = var zero}     = {!   !}
-- lifted-lemma-mon {n = suc n} {τ = var zero} = refl
-- lifted-lemma-mon {n = 0} {τ = var (suc x)}  = {!   !}
-- lifted-lemma-mon {n = suc n} {τ = var (suc x)}  = {!   !}
-- lifted-lemma-mon {n = n} {τ = fun τ₁ τ₂}    = cong₂ fun (lifted-lemma-mon {n = n}) (lifted-lemma-mon {n = n})
-- lifted-lemma-mon {n = n} {τ = lam κ τ}      = cong (lam κ) (lifted-lemma-mon {n = suc n})
-- lifted-lemma-mon {n = n} {τ = app τ₁ τ₂}    = cong₂ app (lifted-lemma-mon {n = n}) (lifted-lemma-mon {n = n})
-- lifted-lemma-mon {n = n} {τ = all κ τ}      = cong (all κ) (lifted-lemma-mon {n = suc n})

-- lemma-mon : substType (extendTypeSubst (λ x → renameType r (s x)) τₛ) τ ≡ substType (extendTypeSubst var τₛ) (renameType (liftIndexRenaming r) (substType (liftTypeSubst s) τ))
-- lemma-mon {r = r} {s = s} {τₛ = τₛ} {τ = τ} = lifted-lemma-mon {n = 0} {r = r} {s = s} {τₛ = τₛ} {τ = τ}


-- substType (extendTypeSubst (λ x → renameType r (s x)) τₛ) τ
-- ≡ substType (extendTypeSubst var τₛ) (renameType (liftIndexRenaming r) (substType (liftTypeSubst s) τ))



lifted-suc-IndexRenaming-commut : liftIndexRenamingN n suc (liftIndexRenamingN n r x) ≡ liftIndexRenamingN (suc n) r (liftIndexRenamingN n suc x)
lifted-suc-IndexRenaming-commut {n = 0}                 = refl
lifted-suc-IndexRenaming-commut {n = suc n} {x = 0}     = refl
lifted-suc-IndexRenaming-commut {n = suc n} {x = suc x} = cong suc (lifted-suc-IndexRenaming-commut {n = n})

suc-IndexRenaming-commut : suc (r x) ≡ liftIndexRenaming r (suc x)
suc-IndexRenaming-commut {r = r} = lifted-suc-IndexRenaming-commut {n = 0} {r = r}

lifted-weakenType-renameType-commut : renameType (liftIndexRenamingN n suc) (renameType (liftIndexRenamingN n r) τ) ≡ renameType (liftIndexRenamingN (suc n) r) (renameType (liftIndexRenamingN n suc) τ)
lifted-weakenType-renameType-commut {n = n} {τ = var x}     = cong var (lifted-suc-IndexRenaming-commut {n = n})
lifted-weakenType-renameType-commut {n = n} {τ = fun τ₁ τ₂} = cong₂ fun (lifted-weakenType-renameType-commut {n = n}) (lifted-weakenType-renameType-commut {n = n})
lifted-weakenType-renameType-commut {n = n} {τ = app τ₁ τ₂} = cong₂ app (lifted-weakenType-renameType-commut {n = n}) (lifted-weakenType-renameType-commut {n = n})
lifted-weakenType-renameType-commut {n = n} {r = r} {τ = lam κ τ}
  rewrite lemma-contract-liftIndexRenaming {n = n} {r = suc}
  rewrite lemma-contract-liftIndexRenaming {n = n} {r = r}
  rewrite lemma-contract-liftIndexRenaming {n = suc n} {r = r}
  = cong (lam κ) (lifted-weakenType-renameType-commut {n = suc n})
lifted-weakenType-renameType-commut {n = n} {r = r} {τ = all κ τ}
  rewrite lemma-contract-liftIndexRenaming {n = n} {r = suc}
  rewrite lemma-contract-liftIndexRenaming {n = n} {r = r}
  rewrite lemma-contract-liftIndexRenaming {n = suc n} {r = r}
  = cong (all κ) (lifted-weakenType-renameType-commut {n = suc n})

weakenType-renameType-commut : weakenType (renameType r τ) ≡ renameType (liftIndexRenaming r) (weakenType τ)
weakenType-renameType-commut = lifted-weakenType-renameType-commut {n = 0}


lifted-IndexRenaming-TypeSubst-comp : renameType (liftIndexRenamingN n r) (liftTypeSubstN n s x) ≡ liftTypeSubstN n (λ x → renameType r (s x)) x
lifted-IndexRenaming-TypeSubst-comp {n = 0}             = refl
lifted-IndexRenaming-TypeSubst-comp {n = suc n} {x = 0} = refl
lifted-IndexRenaming-TypeSubst-comp {n = suc n} {r = r} {s = s} {x = suc x}
  rewrite sym (lemma-contract-liftIndexRenaming {n = n} {r = r})
  rewrite sym (weakenType-renameType-commut {r = liftIndexRenamingN n r} {τ = liftTypeSubstN n s x})
  = cong weakenType (lifted-IndexRenaming-TypeSubst-comp {n = n})

lifted-renameType-substType-comp : renameType (liftIndexRenamingN n r) (substType (liftTypeSubstN n s) τ) ≡ substType (liftTypeSubstN n (λ x → renameType r (s x))) τ
lifted-renameType-substType-comp {n = n} {τ = var x}     = lifted-IndexRenaming-TypeSubst-comp {n = n}
lifted-renameType-substType-comp {n = n} {τ = fun τ₁ τ₂} = cong₂ fun (lifted-renameType-substType-comp {n = n} {τ = τ₁}) (lifted-renameType-substType-comp {n = n} {τ = τ₂})
lifted-renameType-substType-comp {n = n} {τ = app τ₁ τ₂} = cong₂ app (lifted-renameType-substType-comp {n = n} {τ = τ₁}) (lifted-renameType-substType-comp {n = n} {τ = τ₂})
lifted-renameType-substType-comp {n = n} {r = r} {s = s} {τ = lam κ τ}
  rewrite lemma-contract-liftIndexRenaming {n = n} {r = r}
  rewrite lemma-contract-liftTypeSubst {n = n} {s = s}
  rewrite lemma-contract-liftTypeSubst {n = n} {s = (λ x → renameType r (s x))}
  = cong (lam κ) (lifted-renameType-substType-comp {n = suc n} {τ = τ})
lifted-renameType-substType-comp {n = n} {r = r} {s = s} {τ = all κ τ}
  rewrite lemma-contract-liftIndexRenaming {n = n} {r = r}
  rewrite lemma-contract-liftTypeSubst {n = n} {s = s}
  rewrite lemma-contract-liftTypeSubst {n = n} {s = (λ x → renameType r (s x))}
  = cong (all κ) (lifted-renameType-substType-comp {n = suc n} {τ = τ})


lifted-suc-TypeSubst-commut : renameType (liftIndexRenamingN n suc) (liftTypeSubstN n s x) ≡ liftTypeSubstN (suc n) s (liftIndexRenamingN n suc x)
lifted-suc-TypeSubst-commut {n = 0}                 = refl
lifted-suc-TypeSubst-commut {n = suc n} {x = 0}     = refl
lifted-suc-TypeSubst-commut {n = suc n} {s = s} {x = suc x}
  rewrite sym (lemma-contract-liftIndexRenaming {n = n} {r = suc})
  rewrite sym (weakenType-renameType-commut {r = liftIndexRenamingN n suc} {τ = liftTypeSubstN n s x})
  = cong weakenType (lifted-suc-TypeSubst-commut {n = n} {s = s} {x = x})

suc-TypeSubst-commut : renameType suc (s x) ≡ liftTypeSubst s (suc x)
suc-TypeSubst-commut {s = s} = lifted-suc-TypeSubst-commut {n = 0} {s = s}


lifted-weakenType-substType-commut : renameType (liftIndexRenamingN n suc) (substType (liftTypeSubstN n s) τ) ≡ substType (liftTypeSubstN (suc n) s) (renameType (liftIndexRenamingN n suc) τ)
lifted-weakenType-substType-commut {n = n} {τ = var x}     = lifted-suc-TypeSubst-commut {n = n}
lifted-weakenType-substType-commut {n = n} {τ = fun τ₁ τ₂} = cong₂ fun (lifted-weakenType-substType-commut {n = n} {τ = τ₁}) (lifted-weakenType-substType-commut {n = n} {τ = τ₂})
lifted-weakenType-substType-commut {n = n} {τ = app τ₁ τ₂} = cong₂ app (lifted-weakenType-substType-commut {n = n} {τ = τ₁}) (lifted-weakenType-substType-commut {n = n} {τ = τ₂})
lifted-weakenType-substType-commut {n = n} {s = s} {τ = lam κ τ}
  rewrite lemma-contract-liftIndexRenaming {n = n} {r = suc}
  rewrite lemma-contract-liftTypeSubst {n = n} {s = s}
  rewrite lemma-contract-liftTypeSubst {n = suc n} {s = s}
  = cong (lam κ) (lifted-weakenType-substType-commut {n = suc n} {τ = τ})
lifted-weakenType-substType-commut {n = n} {s = s} {τ = all κ τ}
  rewrite lemma-contract-liftIndexRenaming {n = n} {r = suc}
  rewrite lemma-contract-liftTypeSubst {n = n} {s = s}
  rewrite lemma-contract-liftTypeSubst {n = suc n} {s = s}
  = cong (all κ) (lifted-weakenType-substType-commut {n = suc n} {τ = τ})

weakenType-substType-commut : weakenType (substType s τ) ≡ substType (liftTypeSubst s) (weakenType τ)
weakenType-substType-commut {τ = τ} = lifted-weakenType-substType-commut {n = 0} {τ = τ}


lifted-lemma-extendTypeSubst : substType (liftTypeSubstN n (extendTypeSubst var τₛ)) (liftTypeSubstN n (liftTypeSubst s) x) ≡ liftTypeSubstN n (extendTypeSubst s τₛ) x
lifted-lemma-extendTypeSubst {n = 0}     {x = 0}                      = refl
lifted-lemma-extendTypeSubst {n = suc n} {x = 0}                      = refl
lifted-lemma-extendTypeSubst {n = 0}     {τₛ = τₛ} {s = s} {x = suc x} = lemma-substTypeAtZero-weakened {τ = s x} {τₛ = τₛ}
lifted-lemma-extendTypeSubst {n = suc n} {τₛ = τₛ} {s = s} {x = suc x}
  rewrite sym (lemma-contract-liftTypeSubst {n = n} {s = extendTypeSubst var τₛ})
  rewrite sym (weakenType-substType-commut {s = liftTypeSubstN n (extendTypeSubst var τₛ)} {τ = liftTypeSubstN n (liftTypeSubst s) x})
  rewrite sym (suc-TypeSubst-commut {s = liftTypeSubstN n (extendTypeSubst s τₛ)} {x = x})
  = cong weakenType (lifted-lemma-extendTypeSubst {n = n})

lifted-substTypeAtZero-comp : substType (liftTypeSubstN n (extendTypeSubst var τₛ)) (substType (liftTypeSubstN n (liftTypeSubst s)) τ) ≡ substType (liftTypeSubstN n (extendTypeSubst s τₛ)) τ
lifted-substTypeAtZero-comp {n = n} {τ = var x}     = lifted-lemma-extendTypeSubst {n = n}
lifted-substTypeAtZero-comp {n = n} {τ = fun τ₁ τ₂} = cong₂ fun (lifted-substTypeAtZero-comp {n = n} {τ = τ₁}) (lifted-substTypeAtZero-comp {n = n} {τ = τ₂})
lifted-substTypeAtZero-comp {n = n} {τ = app τ₁ τ₂} = cong₂ app (lifted-substTypeAtZero-comp {n = n} {τ = τ₁}) (lifted-substTypeAtZero-comp {n = n} {τ = τ₂})
lifted-substTypeAtZero-comp {n = n} {τₛ = τₛ} {s = s} {τ = lam κ τ}
  rewrite lemma-contract-liftTypeSubst {n = n} {s = extendTypeSubst var τₛ}
  rewrite lemma-contract-liftTypeSubst {n = n} {s = liftTypeSubst s}
  rewrite lemma-contract-liftTypeSubst {n = n} {s = extendTypeSubst s τₛ}
  = cong (lam κ) (lifted-substTypeAtZero-comp {n = suc n} {τ = τ})
lifted-substTypeAtZero-comp {n = n} {τₛ = τₛ} {s = s} {τ = all κ τ}
  rewrite lemma-contract-liftTypeSubst {n = n} {s = extendTypeSubst var τₛ}
  rewrite lemma-contract-liftTypeSubst {n = n} {s = liftTypeSubst s}
  rewrite lemma-contract-liftTypeSubst {n = n} {s = extendTypeSubst s τₛ}
  = cong (all κ) (lifted-substTypeAtZero-comp {n = suc n} {τ = τ})

substTypeAtZero-comp : substType (liftTypeSubst s) τ [ τₛ ] ≡ substType (extendTypeSubst s τₛ) τ
substTypeAtZero-comp {s = s} {τ = τ} {τₛ = τₛ} = lifted-substTypeAtZero-comp {n = 0} {τₛ = τₛ} {s = s} {τ = τ}