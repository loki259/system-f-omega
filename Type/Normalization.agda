{-# OPTIONS --allow-unsolved-metas #-}

module Type.Normalization where

open import Prelude
open import Type
open import Type.Context
open import Type.Kinding
open import Type.Substitution
open import Type.Equality


mutual
  infix 3 _⊢ₙ_∶_
  data _⊢ₙ_∶_ (Δ : KindCtx) : Type → Kind → Set where
    neu : Δ ⊢ᵤ τ ∶ κ → Δ ⊢ₙ τ ∶ κ
    fun : Δ ⊢ₙ τ₁ ∶ ⋆ → Δ ⊢ₙ τ₂ ∶ ⋆ → Δ ⊢ₙ fun τ₁ τ₂ ∶ ⋆
    all : κ ∷ Δ ⊢ₙ τ ∶ ⋆ → Δ ⊢ₙ all κ τ ∶ ⋆
    lam : κ ∷ Δ ⊢ₙ τ ∶ κ' → Δ ⊢ₙ lam κ τ ∶ κ ⇒ κ'

  infix 3 _⊢ᵤ_∶_
  data _⊢ᵤ_∶_ (Δ : KindCtx) : Type → Kind → Set where
    var : Δ ∋ x ↦ κ → Δ ⊢ᵤ var x ∶ κ
    app : Δ ⊢ᵤ τ₁ ∶ κ ⇒ κ' → Δ ⊢ₙ τ₂ ∶ κ → Δ ⊢ᵤ app τ₁ τ₂ ∶ κ'

variable
  τₙ τᵤ : Type


infix 3 _∃⊢ₙ_∶_
record _∃⊢ₙ_∶_ (Δ : KindCtx) (τ : Type) (κ : Kind) : Set where
  field
    normalForm    : Type
    normalization : Δ ⊢ₙ normalForm ∶ κ
    soundness     : Δ ⊢ normalForm ≡ₜ τ ∶ κ
open _∃⊢ₙ_∶_ public

infix 3 _∃⊢ᵤ_∶_
record _∃⊢ᵤ_∶_ (Δ : KindCtx) (τ : Type) (κ : Kind) : Set where
  field
    neutralForm    : Type
    neutralization : Δ ⊢ᵤ neutralForm ∶ κ
    soundness      : Δ ⊢ neutralForm ≡ₜ τ ∶ κ
open _∃⊢ᵤ_∶_ public


infix 3 _⊢ₙ_≡ₜ_∶_
data _⊢ₙ_≡ₜ_∶_ (Δ : KindCtx) : Type → Type → Kind → Set where
  refl : Δ ⊢ₙ τ ∶ κ → Δ ⊢ₙ τ ≡ₜ τ ∶ κ

-- infix 3 _∃⊢ₙ_≡ₜ_∶_
-- record _∃⊢ₙ_≡ₜ_∶_ (Δ : KindCtx) (τ : Type) (τ' : Type) (κ : Kind) : Set where
--   field
--     normalForm     : Type
--     normalForm'    : Type
--     normalEquality : Δ ⊢ₙ normalForm ≡ normalForm' ∶ κ
--     soundness      : Δ ⊢ normalForm ≡ₜ τ ∶ κ
--     soundness'     : Δ ⊢ normalForm' ≡ₜ τ' ∶ κ
-- open _∃⊢ₙ_≡ₜ_∶_ public


mutual
  renameKindingₙ : ∀ {Φ Ψ f} → Renaming Φ Ψ f → ∀ {τ κ} → Φ ⊢ₙ τ ∶ κ → Ψ ⊢ₙ renameType f τ ∶ κ
  renameKindingₙ ρ (neu prf)       = neu (renameKindingᵤ ρ prf)
  renameKindingₙ ρ (fun prf₁ prf₂) = fun (renameKindingₙ ρ prf₁) (renameKindingₙ ρ prf₂)
  renameKindingₙ ρ (all prf)       = all (renameKindingₙ (liftRenaming ρ) prf)
  renameKindingₙ ρ (lam prf)       = lam (renameKindingₙ (liftRenaming ρ) prf)

  renameKindingᵤ : ∀ {Φ Ψ f} → Renaming Φ Ψ f → ∀ {τ κ} → Φ ⊢ᵤ τ ∶ κ → Ψ ⊢ᵤ renameType f τ ∶ κ
  renameKindingᵤ ρ (var prf)       = var (ρ prf)
  renameKindingᵤ ρ (app prf₁ prf₂) = app (renameKindingᵤ ρ prf₁) (renameKindingₙ ρ prf₂)


renameType-eq : Renaming Δ Δ' r → Δ ⊢ τ₁ ≡ₜ τ₂ ∶ κ → Δ' ⊢ renameType r τ₁ ≡ₜ renameType r τ₂ ∶ κ
renameType-eq ρ (trefl prf)      = trefl (renameKinding ρ prf)
renameType-eq ρ (tsym eq)        = tsym (renameType-eq ρ eq)
renameType-eq ρ (ttrans eq₁ eq₂) = ttrans (renameType-eq ρ eq₁) (renameType-eq ρ eq₂)
renameType-eq ρ (fun eq₁ eq₂)    = fun (renameType-eq ρ eq₁) (renameType-eq ρ eq₂)
renameType-eq ρ (all eq)         = all (renameType-eq (liftRenaming ρ) eq)
renameType-eq ρ (lam eq)         = lam (renameType-eq (liftRenaming ρ) eq)
renameType-eq ρ (app eq₁ eq₂)    = app (renameType-eq ρ eq₁) (renameType-eq ρ eq₂)
renameType-eq {r = r} ρ (beta {τ = τ} {τₛ = τₛ} prf)
  rewrite renameType-substType-extendTypeSubst-comp {r = r} {τₛ = τₛ} {τ = τ}
  = beta (renameKinding ρ prf)
renameType-eq {r = r} ρ (eta {τ = τ} prf)
  rewrite sym (weakenType-renameType-commut {r = r} {τ = τ})
  = eta (renameKinding ρ prf)


renameKinding∃ₙ : ∀ {Φ Ψ f} → Renaming Φ Ψ f → ∀ {τ κ} → Φ ∃⊢ₙ τ ∶ κ → Ψ ∃⊢ₙ renameType f τ ∶ κ
renameKinding∃ₙ {f = f} ρ prf .normalForm    = renameType f (prf .normalForm)
renameKinding∃ₙ {f = f} ρ prf .normalization = renameKindingₙ ρ (prf .normalization)
renameKinding∃ₙ {f = f} ρ prf .soundness     = renameType-eq ρ (prf .soundness)

renameKinding∃ᵤ : ∀ {Φ Ψ f} → Renaming Φ Ψ f → ∀ {τ κ} → Φ ∃⊢ᵤ τ ∶ κ → Ψ ∃⊢ᵤ renameType f τ ∶ κ
renameKinding∃ᵤ {f = f} ρ prf .neutralForm    = renameType f (prf .neutralForm)
renameKinding∃ᵤ {f = f} ρ prf .neutralization = renameKindingᵤ ρ (prf .neutralization)
renameKinding∃ᵤ {f = f} ρ prf .soundness      = renameType-eq ρ (prf .soundness)

weakenKindingₙ : Δ ⊢ₙ τ ∶ κ → κ' ∷ Δ ⊢ₙ weakenType τ ∶ κ
weakenKindingₙ = renameKindingₙ there

weakenKindingᵤ : Δ ⊢ᵤ τ ∶ κ → κ' ∷ Δ ⊢ᵤ weakenType τ ∶ κ
weakenKindingᵤ = renameKindingᵤ there


-- Forcing
infix 3 _⊩_∶_
_⊩_∶_ : KindCtx → Type → Kind → Set
Δ ⊩ τ ∶ ⋆         = Δ ∃⊢ₙ τ ∶ ⋆
Δ ⊩ τ ∶ κ ⇒ κ' = ∀ {Δ' r τ'} → Renaming Δ Δ' r → Δ' ⊩ τ' ∶ κ → Δ' ⊩ app (renameType r τ) τ' ∶ κ'


renameForcing : Renaming Δ Δ' r → Δ ⊩ τ ∶ κ → Δ' ⊩ renameType r τ ∶ κ
renameForcing {κ = ⋆} ρ prf = renameKinding∃ₙ ρ prf
renameForcing {r = r} {τ = τ} {κ = κ ⇒ κ₁} ρ f {r = r'} ρ' prf
  with prf' ← f (Renaming-∘ ρ' ρ) prf rewrite lifted-renameType-∘ {n = 0} {r' = r'} {r = r} {τ = τ} = prf'

ForcingSubst : KindCtx → KindCtx → TypeSubst → Set
ForcingSubst Δ Δ' f = ∀ {x κ} → Δ ∋ x ↦ κ → Δ' ⊩ f x ∶ κ

strengthen : RetractableRenaming Δ Δ' r → Δ' ⊢ renameType r τ ∶ κ → Δ ⊢ τ ∶ κ
strengthen {τ = var x}     ρ (var prf)       = var (ρ .retract prf)
strengthen {τ = fun τ₁ τ₂} ρ (fun prf₁ prf₂) = fun (strengthen ρ prf₁) (strengthen ρ prf₂)
strengthen {τ = lam κ τ}   ρ (lam prf)       = lam (strengthen (lift ρ) prf)
strengthen {τ = app τ₁ τ₂} ρ (app prf₁ prf₂) = app (strengthen ρ prf₁) (strengthen ρ prf₂)
strengthen {τ = all κ τ}   ρ (all prf)       = all (strengthen (lift ρ) prf)


η-contract : Δ ⊢ lam κ₁ (app (weakenType τ) (var zero)) ∶ κ₁ ⇒ κ₂ → Δ ⊢ τ ∶ κ₁ ⇒ κ₂
η-contract (lam (app prf (var here))) = strengthen weakenRetraction prf

mutual
  reify : Δ ⊩ τ ∶ κ → Δ ∃⊢ₙ τ ∶ κ
  reify {κ = ⋆} prf = prf
  reify {Δ = Δ} {τ = τ} {κ = κ₁ ⇒ κ₂} f with prf ← reify (f there (reflect var0Eval))
    using eta-eq ← tsym (eta (η-contract (lam (extractKindingFromEquality (prf .soundness) .proj₂))))
    = record { normalForm    = lam κ₁ (prf .normalForm)
             ; normalization = lam (prf .normalization)
             ; soundness     = ttrans (lam (prf .soundness)) eta-eq
             }

  reflect : Δ ∃⊢ᵤ τ ∶ κ → Δ ⊩ τ ∶ κ
  reflect {κ = ⋆} prf = record { normalForm    = (prf .neutralForm)
                               ; normalization = neu (prf .neutralization)
                               ; soundness     = prf .soundness
                               }
  reflect {κ = κ₁ ⇒ κ₂} prf {r = r} ρ prfₛ with prf' ← reify prfₛ
    = reflect record { neutralForm    = app (renameType r (prf .neutralForm)) (prf' .normalForm)
                     ; neutralization = app (renameKindingᵤ ρ (prf .neutralization)) (prf' .normalization)
                     ; soundness      = app (renameType-eq ρ (prf .soundness)) (prf' .soundness)
                     }
  
  var0Eval : κ ∷ Δ ∃⊢ᵤ var zero ∶ κ
  var0Eval = record { neutralForm    = var zero
                    ; neutralization = var here
                    ; soundness      = trefl (var here)
                    }

extendForcingSubst : ForcingSubst Δ Δ' s → Δ' ⊩ τ ∶ κ → ForcingSubst (κ ∷ Δ) Δ' (extendTypeSubst s τ)
extendForcingSubst σ prf here        = prf
extendForcingSubst σ _   (there prf) = σ prf


weakenForcing : ∀ {Δ κ κ' τ} → Δ ⊩ τ ∶ κ → κ' ∷ Δ ⊩ weakenType τ ∶ κ
weakenForcing = renameForcing there

liftForcingSubst : ForcingSubst Δ Δ' s → ForcingSubst (κ ∷ Δ) (κ ∷ Δ') (liftTypeSubst s)
liftForcingSubst σ here        = reflect var0Eval
liftForcingSubst σ (there prf) = weakenForcing (σ prf)


idSubst : ForcingSubst Δ Δ var
idSubst {x = x} prf = reflect record { neutralForm    = var x
                                     ; neutralization = var prf
                                     ; soundness      = trefl (var prf)
                                     }                                     

-- Normalization under all possible substitutions
infix 3 _⊧_∶_
_⊧_∶_ : KindCtx → Type → Kind → Set
Δ ⊧ τ ∶ κ = ∀ {Δ' s} → ForcingSubst Δ Δ' s → Δ' ⊩ substType s τ ∶ κ

extractKindingFromForcing : Δ ⊩ τ ∶ κ → Δ ⊢ τ ∶ κ
extractKindingFromForcing prf = extractKindingFromEquality (reify prf .soundness) .proj₂

castForcing : Δ ⊢ τ ≡ₜ τ' ∶ κ → Δ ⊩ τ ∶ κ → Δ ⊩ τ' ∶ κ
castForcing {κ = ⋆} eq prf = record { normalForm    = prf .normalForm
                                    ; normalization = prf .normalization
                                    ; soundness     = ttrans (prf .soundness) eq
                                    }
castForcing {κ = κ ⇒ κ₁} eq f ρ prfₛ using eq' ← renameType-eq ρ eq
  = castForcing (app eq' (trefl (extractKindingFromForcing prfₛ))) (f ρ prfₛ)


evalKinding : Δ ⊢ τ ∶ κ → Δ ⊧ τ ∶ κ
evalKinding (var prf) σ = σ prf
evalKinding (fun prf₁ prf₂) σ with prf₁' ← evalKinding prf₁ σ | prf₂' ← evalKinding prf₂ σ
  = record { normalForm    = fun (prf₁' .normalForm)    (prf₂' .normalForm)
           ; normalization = fun (prf₁' .normalization) (prf₂' .normalization)
           ; soundness     = fun (prf₁' .soundness)     (prf₂' .soundness)
           }
evalKinding (all prf) σ with prf' ← evalKinding prf (liftForcingSubst σ)
  = record { normalForm    = all _ (prf' .normalForm)
           ; normalization = all (prf' .normalization)
           ; soundness     = all (prf' .soundness)
           }
evalKinding (lam {κ = κ} {τ = τ} {κ' = κ'} prf) {s = s} σ {Δ' = Δ'} {r = r} {τ' = τₛ} ρ prfₛ
  using σ' ← (λ {x = x} {κ = κ} prf → renameForcing ρ (σ {x = x} {κ = κ} prf))
  with prf' ← (evalKinding prf (extendForcingSubst σ' prfₛ))
  with appDeriv ← Type.Kinding.app (substKinding (extractKindingFromForcing ∘ σ') (lam prf)) (extractKindingFromForcing prfₛ)
  rewrite sym (substTypeAtZero-comp {s = λ x → renameType r (s x)} {τ = τ} {τₛ = τₛ})
  rewrite sym (lifted-renameType-substType-comp {n = 1} {r = r} {s = s} {τ = τ})
  using prf'ₖ ← extractKindingFromForcing prf'
  = castForcing (tsym (beta appDeriv)) prf'
evalKinding (app {τ₁ = τ₁} prf₁ prf₂) {s = s} σ with prf ← evalKinding prf₁ σ idRenaming (evalKinding prf₂ σ)
  rewrite renameType-idRenaming-id {τ = substType s τ₁} = prf


normalizeKinding : Δ ⊢ τ ∶ κ → Δ ∃⊢ₙ τ ∶ κ
normalizeKinding {τ = τ} prf with prf' ← reify (evalKinding prf idSubst) rewrite substType-id {τ = τ} = prf'


denormalizeKinding∃ : (prf : Δ ∃⊢ₙ τ ∶ κ) → Δ ⊢ (prf .normalForm) ∶ κ
denormalizeKinding∃ prf = extractKindingFromEquality (prf .soundness) .proj₁

denormalizeKinding : Δ ⊢ₙ τ ∶ κ → Δ ⊢ τ ∶ κ
denormalizeKinding (neu (var prf))       = var prf
denormalizeKinding (neu (app prf₁ prf₂)) = app (denormalizeKinding (neu prf₁)) (denormalizeKinding prf₂)
denormalizeKinding (fun prf₁ prf₂)       = fun (denormalizeKinding prf₁) (denormalizeKinding prf₂)
denormalizeKinding (all prf)             = all (denormalizeKinding prf)
denormalizeKinding (lam prf)             = lam (denormalizeKinding prf)


normalizationSoundness : (prf : Δ ⊢ τ ∶ κ) → Δ ⊢ normalizeKinding prf .normalForm ≡ₜ τ ∶ κ
normalizationSoundness prf = normalizeKinding prf .soundness


-- normalizeTypeEquality : Δ ⊢ τ ≡ₜ τ' ∶ κ → Δ ∃⊢ₙ τ ≡ₜ τ' ∶ κ
normalizeTypeEquality : (eq : Δ ⊢ τ ≡ₜ τ' ∶ κ) → Δ ⊢ₙ normalizeKinding (extractKindingFromEquality eq .proj₁) .normalForm ≡ₜ normalizeKinding (extractKindingFromEquality eq .proj₂) .normalForm ∶ κ
normalizeTypeEquality eq = {!   !}


denormalizeTypeEquality : Δ ⊢ₙ τ ≡ₜ τ' ∶ κ → Δ ⊢ τ ≡ₜ τ' ∶ κ
denormalizeTypeEquality (refl prf) = trefl (denormalizeKinding prf)


normalizationStability : (prfₙ : Δ ∃⊢ₙ τ ∶ κ) → ∀ {prf : Δ ⊢ prfₙ .normalForm ∶ κ} → Δ ⊢ₙ normalizeKinding prf .normalForm ≡ₜ prfₙ .normalForm ∶ κ
normalizationStability prfₙ {prf = prf} = {!   !}


normalizationUniqueness : (prf : Δ ∃⊢ₙ τ ∶ κ) → (prf' : Δ ∃⊢ₙ τ ∶ κ) → Δ ⊢ₙ prf .normalForm ≡ₜ prf' .normalForm ∶ κ
normalizationUniqueness prf prf'
  using eq ← ttrans (prf .soundness) (tsym (prf' .soundness))
  with eqₙ ← normalizeTypeEquality eq
  with normalizeKinding (extractKindingFromEquality eq .proj₁) .normalForm | normalizationStability prf {prf = extractKindingFromEquality eq .proj₁}
... | _ | refl _
  with normalizeKinding (extractKindingFromEquality eq .proj₂) .normalForm | normalizationStability prf' {prf = extractKindingFromEquality eq .proj₂}
... | _ | refl _ = eqₙ