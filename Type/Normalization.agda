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
    lam : κ ∷ Δ ⊢ₙ τ ∶ κ' → Δ ⊢ₙ lam κ τ ∶ tfun κ κ'

  infix 3 _⊢ᵤ_∶_
  data _⊢ᵤ_∶_ (Δ : KindCtx) : Type → Kind → Set where
    var : Δ ∋ x ↦ κ → Δ ⊢ᵤ var x ∶ κ
    app : Δ ⊢ᵤ τ₁ ∶ tfun κ κ' → Δ ⊢ₙ τ₂ ∶ κ → Δ ⊢ᵤ app τ₁ τ₂ ∶ κ'

variable
  τₙ τᵤ : Type

infix 3 _∃⊢ₙ_∶_
_∃⊢ₙ_∶_ : KindCtx → Type → Kind → Set
Δ ∃⊢ₙ τ ∶ κ = ∃[ τ' ] (Δ ⊢ₙ τ' ∶ κ) × (Δ ⊢ τ' ≡ₜ τ ∶ κ)

infix 3 _∃⊢ᵤ_∶_
_∃⊢ᵤ_∶_ : KindCtx → Type → Kind → Set
Δ ∃⊢ᵤ τ ∶ κ = ∃[ τ' ] (Δ ⊢ᵤ τ' ∶ κ) × (Δ ⊢ τ' ≡ₜ τ ∶ κ)

-- infix 3 _∃⊢ₙ_∶_
-- record _∃⊢ₙ_∶_ (Δ : KindCtx) (τ : Type) (κ : Kind) : Set where
--   field
--     {τₙ}          : Type
--     normalization : Δ ⊢ₙ τₙ ∶ κ
--     soundness     : Δ ⊢ τₙ ≡ₜ τ ∶ κ

-- infix 3 _∃⊢ᵤ_∶_
-- record _∃⊢ᵤ_∶_ (Δ : KindCtx) (τ : Type) (κ : Kind) : Set where
--   field
--     {τᵤ}           : Type
--     neutralization : Δ ⊢ᵤ τᵤ ∶ κ
--     soundness      : Δ ⊢ τᵤ ≡ₜ τ ∶ κ

infix 3 _⊢ₙ_≡ₜ_∶_
data _⊢ₙ_≡ₜ_∶_ (Δ : KindCtx) : Type → Type → Kind → Set where
  refl : Δ ⊢ₙ τ ∶ κ → Δ ⊢ₙ τ ≡ₜ τ ∶ κ

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
renameKinding∃ₙ {f = f} ρ ⟨ τ' , ⟨ prf , eq ⟩ ⟩ = ⟨ renameType f τ' , ⟨ renameKindingₙ ρ prf , renameType-eq ρ eq ⟩ ⟩

renameKinding∃ᵤ : ∀ {Φ Ψ f} → Renaming Φ Ψ f → ∀ {τ κ} → Φ ∃⊢ᵤ τ ∶ κ → Ψ ∃⊢ᵤ renameType f τ ∶ κ
renameKinding∃ᵤ {f = f} ρ ⟨ τ' , ⟨ prf , eq ⟩ ⟩ = ⟨ renameType f τ' , ⟨ renameKindingᵤ ρ prf , renameType-eq ρ eq ⟩ ⟩

weakenKindingₙ : Δ ⊢ₙ τ ∶ κ → κ' ∷ Δ ⊢ₙ weakenType τ ∶ κ
weakenKindingₙ = renameKindingₙ there

weakenKindingᵤ : Δ ⊢ᵤ τ ∶ κ → κ' ∷ Δ ⊢ᵤ weakenType τ ∶ κ
weakenKindingᵤ = renameKindingᵤ there


-- Forcing
infix 3 _⊩_∶_
_⊩_∶_ : KindCtx → Type → Kind → Set
Δ ⊩ τ ∶ ⋆         = Δ ∃⊢ₙ τ ∶ ⋆
Δ ⊩ τ ∶ tfun κ κ' = ∀ {Δ' r τ'} → Renaming Δ Δ' r → Δ' ⊩ τ' ∶ κ → Δ' ⊩ app (renameType r τ) τ' ∶ κ'


renameForcing : Renaming Δ Δ' r → Δ ⊩ τ ∶ κ → Δ' ⊩ renameType r τ ∶ κ
renameForcing {κ = ⋆} ρ prf = renameKinding∃ₙ ρ prf
renameForcing {r = r} {τ = τ} {κ = tfun κ κ₁} ρ f {r = r'} ρ' prf
  with prf' ← f (Renaming-∘ ρ' ρ) prf rewrite lifted-renameType-∘ {n = 0} {r' = r'} {r = r} {τ = τ} = prf'

ForcingSubst : KindCtx → KindCtx → TypeSubst → Set
ForcingSubst Δ Δ' f = ∀ {x κ} → Δ ∋ x ↦ κ → Δ' ⊩ f x ∶ κ

strengthen : RetractableRenaming Δ Δ' r → Δ' ⊢ renameType r τ ∶ κ → Δ ⊢ τ ∶ κ
strengthen {τ = var x}     ρ (var prf)       = var (ρ .retract prf)
strengthen {τ = fun τ₁ τ₂} ρ (fun prf₁ prf₂) = fun (strengthen ρ prf₁) (strengthen ρ prf₂)
strengthen {τ = lam κ τ}   ρ (lam prf)       = lam (strengthen (lift ρ) prf)
strengthen {τ = app τ₁ τ₂} ρ (app prf₁ prf₂) = app (strengthen ρ prf₁) (strengthen ρ prf₂)
strengthen {τ = all κ τ}   ρ (all prf)       = all (strengthen (lift ρ) prf)

-- mutual
--   strengthenₙ : RetractableRenaming Δ Δ' r → Δ' ⊢ₙ renameType r τ ∶ κ → Δ ⊢ₙ τ ∶ κ
--   strengthenₙ {τ = var x}     ρ (neu prfᵤ)      = neu (strengthenᵤ ρ prfᵤ)
--   strengthenₙ {τ = fun τ₁ τ₂} ρ (fun prf₁ prf₂) = fun (strengthenₙ ρ prf₁) (strengthenₙ ρ prf₂)
--   strengthenₙ {τ = lam κ τ}   ρ (lam prf)       = lam (strengthenₙ (lift ρ) prf)
--   strengthenₙ {τ = app τ₁ τ₂} ρ (neu prfᵤ)      = neu (strengthenᵤ ρ prfᵤ)
--   strengthenₙ {τ = all κ τ}   ρ (all prf)       = all (strengthenₙ (lift ρ) prf)

--   strengthenᵤ : RetractableRenaming Δ Δ' r → Δ' ⊢ᵤ renameType r τ ∶ κ → Δ ⊢ᵤ τ ∶ κ
--   strengthenᵤ {τ = var x}     ρ (var prf)       = var (ρ .retract prf)
--   strengthenᵤ {τ = app τ₁ τ₂} ρ (app prf₁ prf₂) = app (strengthenᵤ ρ prf₁) (strengthenₙ ρ prf₂)

-- invertHere : κ' ∷ Δ ∋ zero ↦ κ → κ ≡ κ'
-- invertHere here = refl

-- η-contract : κ' ∷ Δ ⊢ₙ weakenType τ [ var zero ] ∶ κ₂ → Δ ⊢ₙ τ ∶ tfun κ' κ₂
-- η-contract (neu (app prf₁ (neu (var prf₂)))) rewrite invertHere prf₂ = neu (strengthenᵤ weakenRetraction prf₁)

-- substKindingHereᵤ : ∀ {Φ κ κ' τ τₛ} → κ ∷ Φ ⊢ᵤ τ ∶ κ' → Φ ⊢ₙ τₛ ∶ κ → Φ ⊢ᵤ τ [ τₛ ] ∶ κ'
-- substKindingHereᵤ = {!   !}

denormalizeKinding : Δ ⊢ₙ τ ∶ κ → Δ ⊢ τ ∶ κ
denormalizeKinding (neu (var prf))       = var prf
denormalizeKinding (neu (app prf₁ prf₂)) = app (denormalizeKinding (neu prf₁)) (denormalizeKinding prf₂)
denormalizeKinding (fun prf₁ prf₂)       = fun (denormalizeKinding prf₁) (denormalizeKinding prf₂)
denormalizeKinding (all prf)             = all (denormalizeKinding prf)
denormalizeKinding (lam prf)             = lam (denormalizeKinding prf)

η-contract : Δ ⊢ lam κ₁ (app (weakenType τ) (var zero)) ∶ tfun κ₁ κ₂ → Δ ⊢ τ ∶ tfun κ₁ κ₂
η-contract (lam (app prf (var here))) = strengthen weakenRetraction prf

mutual
  reify : Δ ⊩ τ ∶ κ → Δ ∃⊢ₙ τ ∶ κ
  reify {κ = ⋆} prf = prf
  reify {Δ = Δ} {τ = τ} {κ = tfun κ₁ κ₂} f with reify (f there (reflect ⟦var0⟧))
  ... | ⟨ τ' , ⟨ prf , eq ⟩ ⟩
    using eta-eq ← tsym (eta (η-contract (lam (extractKinding eq .proj₂))))
    = ⟨ lam κ₁ τ' , ⟨ lam prf , ttrans (lam eq) eta-eq ⟩ ⟩

  reflect : Δ ∃⊢ᵤ τ ∶ κ → Δ ⊩ τ ∶ κ
  reflect {κ = ⋆}          ⟨ τ' , ⟨ prfᵤ , eq ⟩ ⟩ = ⟨ τ' , ⟨ neu prfᵤ , eq ⟩ ⟩
  reflect {κ = tfun κ₁ κ₂} ⟨ τ' , ⟨ prfᵤ , eq ⟩ ⟩ {r = r} ρ prf with reify prf
  ... | ⟨ τ₁ , ⟨ prf₁ , eq₁ ⟩ ⟩
    using eq' ← renameType-eq ρ eq
    using prfᵤ' ← renameKindingᵤ ρ prfᵤ
    using ⟨ prfₐ , prfₘ ⟩ ← extractKinding eq₁
    = reflect ⟨ app (renameType r τ') τ₁ , ⟨ app prfᵤ' prf₁ , app eq' eq₁ ⟩ ⟩
  
  ⟦var0⟧ : κ ∷ Δ ∃⊢ᵤ var zero ∶ κ
  ⟦var0⟧ = ⟨ var zero , ⟨ var here , trefl (var here) ⟩ ⟩


extendForcingSubst : ForcingSubst Δ Δ' s → Δ' ⊩ τ ∶ κ → ForcingSubst (κ ∷ Δ) Δ' (extendTypeSubst s τ)
extendForcingSubst σ prf here        = prf
extendForcingSubst σ _   (there prf) = σ prf

-- renameForcing : ∀ {Δ Δ' f τ κ} → Renaming Δ Δ' f → Δ ⊩ τ ∶ κ → Δ' ⊩ renameType f τ ∶ κ
-- renameForcing {κ = ⋆}         ρ prf = renameKindingᵤ ρ prf
-- renameForcing {κ = tfun κ κ'} ρ prf = {!   !}
-- -- renameReducibility {κ = ⋆} ρ (var prf)       = var (ρ prf)
-- -- renameReducibility ρ (fun prf₁ prf₂) = fun (renameReducibility ρ prf₁) (renameReducibility ρ prf₂)
-- -- renameReducibility ρ (all prf)       = all (renameReducibility (liftRenaming ρ) prf)
-- -- renameReducibility ρ (lam prf)       = lam (renameReducibility (liftRenaming ρ) prf)
-- -- renameReducibility ρ (app prf₁ prf₂) = app (renameReducibility ρ prf₁) (renameReducibility ρ prf₂)

weakenForcing : ∀ {Δ κ κ' τ} → Δ ⊩ τ ∶ κ → κ' ∷ Δ ⊩ weakenType τ ∶ κ
weakenForcing = renameForcing there

liftForcingSubst : ForcingSubst Δ Δ' s → ForcingSubst (κ ∷ Δ) (κ ∷ Δ') (liftTypeSubst s)
liftForcingSubst σ here        = reflect ⟦var0⟧ -- reflect (var here)
liftForcingSubst σ (there prf) = weakenForcing (σ prf)


idSubst : ForcingSubst Δ Δ var
idSubst {x = x} prf = reflect ⟨ var x , ⟨ var prf , trefl (var prf) ⟩ ⟩


-- Normalization under all possible substitutions
infix 3 _⊧_∶_
_⊧_∶_ : KindCtx → Type → Kind → Set
Δ ⊧ τ ∶ κ = ∀ {Δ' s} → ForcingSubst Δ Δ' s → Δ' ⊩ substType s τ ∶ κ

extractKindingFromForcing : Δ ⊩ τ ∶ κ → Δ ⊢ τ ∶ κ
extractKindingFromForcing prf using ⟨ _ , ⟨ _ , eq ⟩ ⟩ ← reify prf = extractKinding eq .proj₂

castForcing : Δ ⊢ τ ≡ₜ τ' ∶ κ → Δ ⊩ τ ∶ κ → Δ ⊩ τ' ∶ κ
castForcing {κ = ⋆} eq ⟨ τₙ , ⟨ prfₙ , eqₙ ⟩ ⟩ = ⟨ τₙ , ⟨ prfₙ , ttrans eqₙ eq ⟩ ⟩
castForcing {κ = tfun κ κ₁} eq f ρ prfₛ using eq' ← renameType-eq ρ eq
  = castForcing (app eq' (trefl (extractKindingFromForcing prfₛ))) (f ρ prfₛ)

⟦_⟧ₓ : Δ ∋ x ↦ κ → Δ ⊧ var x ∶ κ
⟦ prf ⟧ₓ σ = σ prf

⟦_⟧ : Δ ⊢ τ ∶ κ → Δ ⊧ τ ∶ κ
⟦ var prf ⟧ σ = ⟦ prf ⟧ₓ σ
⟦ fun prf₁ prf₂ ⟧ σ with ⟦ prf₁ ⟧ σ | ⟦ prf₂ ⟧ σ
... | ⟨ τ₁ , ⟨ prf₁' , eq₁ ⟩ ⟩ | ⟨ τ₂ , ⟨ prf₂' , eq₂ ⟩ ⟩
  = ⟨ fun τ₁ τ₂ , ⟨ fun prf₁' prf₂' , fun eq₁ eq₂ ⟩ ⟩
⟦ all prf ⟧ σ with ⟦ prf ⟧ (liftForcingSubst σ)
... | ⟨ τ' , ⟨ prf' , eq ⟩ ⟩ = ⟨ all _ τ' , ⟨ all prf' , all eq ⟩ ⟩
⟦ lam {κ = κ} {κ' = κ'} {τ = τ} prf ⟧ {s = s} σ {Δ' = Δ'} {r = r} {τ' = τₛ} ρ prfₛ
  using σ' ← (λ {x = x} {κ = κ} prf → renameForcing ρ (σ {x = x} {κ = κ} prf))
  with prf' ← (⟦ prf ⟧ (extendForcingSubst σ' prfₛ))
  with appDeriv ← Type.Kinding.app (substKinding (extractKindingFromForcing ∘ σ') (lam prf)) (extractKindingFromForcing prfₛ)
  rewrite sym (substTypeAtZero-comp {s = λ x → renameType r (s x)} {τ = τ} {τₛ = τₛ})
  rewrite sym (lifted-renameType-substType-comp {n = 1} {r = r} {s = s} {τ = τ})
  using prf'ₖ ← extractKindingFromForcing prf'
  = castForcing (tsym (beta appDeriv)) prf'
⟦ app {τ₁ = τ₁} prf₁ prf₂ ⟧ {s = s} σ with prf ← ⟦ prf₁ ⟧ σ idRenaming (⟦ prf₂ ⟧ σ)
  rewrite renameType-idRenaming-id {τ = substType s τ₁} = prf

-- Lemma: application is valid
-- apply : Γ ⊧ A ⇒ B → Γ ⊧ A → Γ ⊧ B
-- apply f g ρ = f ρ id (g ρ)


normalizeKinding : Δ ⊢ τ ∶ κ →  Δ ∃⊢ₙ τ ∶ κ
normalizeKinding {τ = τ} prf with prf' ← reify (⟦ prf ⟧ idSubst) rewrite substType-id {τ = τ} = prf'