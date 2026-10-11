{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --allow-incomplete-matches #-}

module Typing where

open import Prelude
open import Syntax
open import Context
open import Kinding
open import TypeSubstitution


TypeCtx : Set
TypeCtx = Ctx Type

variable
  Γ : TypeCtx


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

_≟ₜ_ : (τ τ' : Typeₙ) → Dec (τ ≡ τ')
τ₁ ≟ₜ τ₂ = {!   !}

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

mutual
  infix 3 _⊢ₙ_∶_
  data _⊢ₙ_∶_ (Δ : KindCtx) : Typeₙ → Kind → Set where
    neu : ∀ {τ} → Δ ⊢ᵤ τ ∶ ⋆ → Δ ⊢ₙ neu τ ∶ ⋆
    fun : ∀ {τ τ'} → Δ ⊢ₙ τ ∶ ⋆ → Δ ⊢ₙ τ' ∶ ⋆ → Δ ⊢ₙ fun τ τ' ∶ ⋆
    all : ∀ {κ τ} → κ ∷ Δ ⊢ₙ τ ∶ ⋆ → Δ ⊢ₙ all κ τ ∶ ⋆
    lam : ∀ {κ κ' τ} → κ ∷ Δ ⊢ₙ τ ∶ κ' → Δ ⊢ₙ lam κ τ ∶ tfun κ κ'

  infix 3 _⊢ᵤ_∶_
  data _⊢ᵤ_∶_ (Δ : KindCtx) : Typeᵤ → Kind → Set where
    var : ∀ {x} → Δ ∋ x ↦ κ → Δ ⊢ᵤ var x ∶ κ
    app : ∀ {τ τ' κ κ'} → Δ ⊢ᵤ τ ∶ tfun κ κ' → Δ ⊢ₙ τ' ∶ κ → Δ ⊢ᵤ app τ τ' ∶ κ'

TypeCtxₙ : Set
TypeCtxₙ = Ctx Typeₙ

variable
  Γₙ : TypeCtxₙ
  τₙ : Typeₙ

normalizeType : Type → Typeₙ
normalizeType = {!   !}

denormalizeType : Typeₙ → Type
denormalizeType = {!   !}

normalizeTypeCtx : TypeCtx → TypeCtxₙ
normalizeTypeCtx = {!   !} 

denormalizeTypeCtx : TypeCtxₙ → TypeCtx
denormalizeTypeCtx = {!   !}

postulate
  _[_]ₙ : Typeₙ → Typeₙ → Typeₙ
  substTypingHereₙ : ∀ {Φ κ κ' τ τₛ} → κ ∷ Φ ⊢ₙ τ ∶ κ' → Φ ⊢ₙ τₛ ∶ κ → Φ ⊢ₙ τ [ τₛ ]ₙ ∶ κ'

infix 3 _,_⊢_∶ₙ_
data _,_⊢_∶ₙ_ (Δ : KindCtx) (Γₙ : TypeCtxₙ) : Term → Typeₙ → Set where
  var : ∀ {x τₙ}
    → Δ ⊢ₙ τₙ ∶ ⋆
    → Γₙ ∋ x ↦ τₙ
    → Δ , Γₙ ⊢ var x ∶ₙ τₙ
  lam : ∀ {τ τₙ τₙ' t}
    → Δ ⊢ₙ fun τₙ τₙ' ∶ ⋆
    → Δ ⊢ₙ τₙ ∶ ⋆
    → Δ , τₙ ∷ Γₙ ⊢ t ∶ₙ τₙ'
    → Δ , Γₙ ⊢ lam τ t ∶ₙ fun (normalizeType τ) τₙ'
  app : ∀ {τₙ τₙ' t t'}
    → Δ ⊢ₙ τₙ' ∶ ⋆
    → Δ , Γₙ ⊢ t ∶ₙ fun τₙ τₙ'
    → Δ , Γₙ ⊢ t' ∶ₙ τₙ
    → Δ , Γₙ ⊢ app t t' ∶ₙ τₙ'
  tlam : ∀ {κ τₙ t}
    → Δ ⊢ₙ all κ τₙ ∶ ⋆
    → κ ∷ Δ , Γₙ ⊢ t ∶ₙ τₙ
    → Δ , Γₙ ⊢ tlam κ t ∶ₙ all κ τₙ
  tapp : ∀ {κ τₙ t τₛ}
    → Δ ⊢ₙ τₙ [ normalizeType τₛ ]ₙ ∶ ⋆
    → Δ , Γₙ ⊢ t ∶ₙ all κ τₙ
    → Δ ⊢ₙ normalizeType τₛ ∶ κ
    → Δ , Γₙ ⊢ tapp t τₛ ∶ₙ τₙ [ normalizeType τₛ ]ₙ

-- renameTypeᵤ-id : ∀ {Φ J} (A : Φ ⊢ᵤ J) → renameTypeᵤ id A ≡ A
-- renameTypeᵤ-comp : ∀ {Φ Ψ Θ}{ρ : Renaming Φ Ψ} {ρ' : Renaming Ψ Θ} {J} (A : Φ ⊢ᵤ J)
--                  → renameTypeᵤ (ρ' ◦ ρ) A ≡ renameTypeᵤ ρ' (renameTypeᵤ ρ A)


infix 1 _⟶w_

data _⟶w_ : (τ τ' : Type) → Set where
  beta : ∀ {τ τₛ κ} → app (lam κ τ) τₛ ⟶w τ [ τₛ ]
  appl : ∀ {τ τ' τₛ} → τ ⟶w τ' → app τ τₛ ⟶w app τ' τₛ

mutual
  data WNe : Type → Set where
    var : ∀ {x : Nat} → WNe (var x)
    app : ∀ {τ₁ τ₂ : Type} → (wne : WNe τ₁) (wn : WN τ₂) → WNe (app τ₁ τ₂)

  data WN : Type → Set where
    neu : ∀ {τ} → WNe τ → WN τ
    lam : ∀ {τ κ} → WN τ → WN (lam κ τ)
    all : ∀ {τ κ} → WN τ → WN (all κ τ)
    fun : ∀ {τ₁ τ₂} → WN τ₁ → WN τ₂ → WN (fun τ₁ τ₂)
    exp : ∀ {τ τ'} → τ ⟶w τ' → WN τ' → WN τ

-- Red : (Γ : Context) (a : Ty) (t : Term Γ a) → Set
-- Red Γ (` α)   t = WN t
-- Red Γ (a ⇒ b) t = ∀{Δ} (ρ : Wk Δ Γ) {u : Term Δ a} (⟦u⟧ : Red Δ a u) → Red Δ b (app (wk ρ t) u)
_⊩_∶_ : KindCtx → Type → Kind → Set
Δ ⊩ τ ∶ ⋆         = WN τ
Δ ⊩ τ ∶ tfun κ κ' = ∀ {Δ' f} {ρ : Renaming Δ Δ' f} {τ' : Type} → Δ' ⊩ τ' ∶ κ → Δ' ⊩ app (renameType f τ) τ' ∶ κ'

normalization : Δ ⊢ τ ∶ κ → WN τ
normalization prf = {! subst WN (sub-id) (Red→WN (fund t ⟦idS⟧)) !}


lemma : WN τ → Δ ⊢ₙ normalizeType τ ∶ κ
lemma = {!   !} -- WN τ → wn τ → Δ ⊢ₙ normalizeType τ ∶ κ


normalizeKinding : Δ ⊢ τ ∶ κ → Δ ⊢ₙ normalizeType τ ∶ κ
normalizeKinding prf = lemma (normalization prf)

normalizeTyping : Δ , Γ ⊢ e ∶ τ → Δ , normalizeTypeCtx Γ ⊢ e ∶ₙ normalizeType τ 
normalizeTyping = {!   !}

denormalizeTyping : Δ , Γₙ ⊢ e ∶ₙ τₙ → Δ , denormalizeTypeCtx Γₙ ⊢ e ∶ denormalizeType τₙ
denormalizeTyping = {!   !}


dom≡ₜ : ∀ {Δ τ₁ τ₁' τ₂ τ₂'} → Δ ⊢ fun τ₁ τ₂ ≡ₜ fun τ₁' τ₂' ∶ ⋆ → Δ ⊢ τ₁ ≡ₜ τ₁' ∶ ⋆
dom≡ₜ = {!!}
--dom≡ₜ trefl = trefl
--dom≡ₜ (tsym eq) = tsym (dom≡ₜ eq)
--dom≡ₜ (ttrans eq₁ eq₂) = {! !}
--dom≡ₜ (fun eq₁ _) = eq₁

rng≡ₜ : ∀ {Δ τ₁ τ₁' τ₂ τ₂'} → Δ ⊢ fun τ₁ τ₂ ≡ₜ fun τ₁' τ₂' ∶ ⋆ → Δ ⊢ τ₂ ≡ₜ τ₂' ∶ ⋆
rng≡ₜ = {!!}
--rng≡ₜ trefl = trefl
--rng≡ₜ (tsym eq) = tsym (rng≡ₜ eq)
--rng≡ₜ (ttrans eq₁ eq₂) = {!   !}
--rng≡ₜ (fun _ eq₂) = eq₂

uniq-⊢ₜ : ∀ {Δ Γ t τ τ'} → Δ , Γ ⊢ t ∶ₙ τ → Δ , Γ ⊢ t ∶ₙ τ' → τ ≡ τ'
uniq-⊢ₜ = {!   !}

decFun : (Δ : KindCtx) → (τ : Type) → Dec (∃[ τ₁ ] ∃[ τ₂ ] Δ ⊢ τ ≡ₜ fun τ₁ τ₂ ∶ ⋆)
decFun Δ τ = {!   !}

decAll : (Δ : KindCtx) → (τ : Type) → Dec (∃[ κ ] ∃[ τ' ] Δ ⊢ τ ≡ₜ all κ τ' ∶ ⋆)
decAll Δ τ = {!   !}

postulate
  checkKindₙ : ∀ (Δ : KindCtx) (κ : Kind) (τₙ : Typeₙ) → Dec (Δ ⊢ₙ τₙ ∶ κ)
  uniq-⊢ₖₙ : ∀ {Δ τ κ κ'} → Δ ⊢ₙ τ ∶ κ → Δ ⊢ₙ τ ∶ κ' → κ ≡ κ'
  lemma₁ : ∀ {Δ τ κ} → Δ ⊢ τ ∶ κ → Δ ⊢ₙ normalizeType τ ∶ κ
  lemma₂ : ∀ {Δ τ κ} → Δ ⊢ₙ τₙ ∶ κ → Δ ⊢ denormalizeType τₙ ∶ κ

mutual
  inferTypeₙ : ∀ (Δ : KindCtx) (Γ : TypeCtxₙ) (e : Term) → Dec (∃[ τ ] Δ , Γ ⊢ e ∶ₙ τ)
  inferTypeₙ Δ Γ (var x) with find Γ x
  ... | no ref = no λ { ⟨ τ , var _ prf ⟩ → ref ⟨ τ , prf ⟩ }
  ... | yes ⟨ τ , prf ⟩ with checkKindₙ Δ ⋆ τ
  ...   | no ref = no λ { ⟨ τ' , var prfₖ prf' ⟩ → case uniq-∋ prf prf' of λ { refl → ref prfₖ } }
  ...   | yes prfₖ = yes ⟨ τ , var prfₖ prf ⟩
  inferTypeₙ Δ Γ (lam τ e) with checkKindₙ Δ ⋆ (normalizeType τ)
  ... | no ref = no λ { ⟨ fun τ τ' , lam _ prf₁ _ ⟩ → ref {! prf₁  !} }
  ... | yes prfₖ₁ with inferTypeₙ Δ (normalizeType τ ∷ Γ) e
  ...   | no ref = no λ { ⟨ fun τ τ' , lam _ _ prf₂ ⟩ → ref ⟨ τ' , {! prf₂ !} ⟩ }
  ...   | yes ⟨ τ' , prf₂ ⟩ with checkKindₙ Δ ⋆ τ'
  ...     | no ref = no λ { ⟨ fun τ τ' , lam (fun _ prfₖ₂) _ prf₂' ⟩ → case uniq-⊢ₜ prf₂ {! prf₂' !} of λ { refl → ref prfₖ₂ } }
  ...     | yes prfₖ₂ = yes ⟨ fun (normalizeType τ) τ' , lam (fun prfₖ₁ prfₖ₂) prfₖ₁ prf₂ ⟩
  inferTypeₙ Δ Γ (app e₁ e₂) with inferTypeₙ Δ Γ e₁
  ... | no ref = no λ { ⟨ τ' , app _ prf₁ _ ⟩ → ref ⟨ fun _ τ' , prf₁ ⟩ }
  -- ... | yes ⟨ τ , prf₁ ⟩ = no λ { ⟨ τ , app _ prf₁' _ ⟩ → case (uniq-⊢ₜ prf₁ prf₁') of {!   !} }
  ... | yes ⟨ fun τ τ' , prf₁ ⟩ with checkTypeₙ Δ Γ τ e₂
  ...   | no ref = no λ { ⟨ τ , app _ prf₁' prf₂ ⟩ → case uniq-⊢ₜ prf₁ prf₁' of λ { refl → ref prf₂ } }
  ...   | yes prf₂ with checkKindₙ Δ ⋆ τ'
  ...     | no ref = no λ { ⟨ τ , app prfₖ prf₁' _ ⟩ → case uniq-⊢ₜ prf₁ prf₁' of λ { refl → ref prfₖ } }
  ...     | yes prfₖ = yes ⟨ τ' , app prfₖ prf₁ prf₂ ⟩
  inferTypeₙ Δ Γ (tlam κ e) with inferTypeₙ (κ ∷ Δ) Γ e
  ... | no ref = no λ { ⟨ all κ τ , tlam _ prf ⟩ → ref ⟨ τ , prf ⟩ }
  ... | yes ⟨ τ , prf ⟩ with checkKindₙ (κ ∷ Δ) ⋆ τ
  ...   | no ref = no λ { ⟨ all κ τ , tlam (all prfₖ) prf' ⟩ → case uniq-⊢ₜ prf prf' of λ { refl → ref prfₖ } }
  ...   | yes prfₖ = yes ⟨ all κ τ , tlam (all prfₖ) prf ⟩
  inferTypeₙ Δ Γ (tapp e τₛ) with inferTypeₙ Δ Γ e
  ... | no ref = no λ { ⟨ τ , tapp _ prf prfₖ ⟩ → ref ⟨ all _ _ , prf ⟩ }
  -- ... | yes ⟨ τ' , prf ⟩ = no {!   !}
  ... | yes ⟨ all κ τ , prf ⟩ with checkKindₙ Δ κ (normalizeType τₛ)
  ...   | no ref = no λ { ⟨ τ , tapp _ prf' prfₖ ⟩ → case uniq-⊢ₜ prf prf' of λ { refl → ref prfₖ } }
  ...   | yes prfₖₛ with checkKindₙ (κ ∷ Δ) ⋆ τ
  ...     | no ref = no λ { _ → case prf of λ { (tlam (all prfₖ) _) → ref prfₖ } }
  ...     | yes prfₖ = yes ⟨ τ [ normalizeType τₛ ]ₙ , tapp (substTypingHereₙ prfₖ prfₖₛ) prf prfₖₛ ⟩

  checkTypeₙ : ∀ (Δ : KindCtx) (Γ : TypeCtxₙ) (τ : Typeₙ) (e : Term) → Dec (Δ , Γ ⊢ e ∶ₙ τ)
  checkTypeₙ Δ Γ τ e with inferTypeₙ Δ Γ e
  ... | no ref = no λ prf → ref ⟨ τ , prf ⟩
  ... | yes ⟨ τ' , prf ⟩ with τ' ≟ₜ τ
  ...   | no ref   = no λ prf' → ref (uniq-⊢ₜ prf prf')
  ...   | yes refl = yes prf




inferType : ∀ (Δ : KindCtx) (Γ : TypeCtx) (e : Term) → Dec (∃[ τ ] Δ , Γ ⊢ e ∶ τ)
inferType Δ Γ e with inferTypeₙ Δ (normalizeTypeCtx Γ) e
... | no ref = no λ { ⟨ τ , prf ⟩ → ref ⟨ normalizeType τ , normalizeTyping prf ⟩ }
... | yes ⟨ τₙ , prfₙ ⟩ = yes ⟨ denormalizeType τₙ , denormalizeTyping prfₙ ⟩