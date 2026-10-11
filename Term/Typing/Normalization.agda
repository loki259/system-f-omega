module Term.Typing.Normalization where

open import Prelude
open import Term
open import Term.Context

-- mutual
--   data Typeₙ : Set where
--     neu : Typeᵤ → Typeₙ
--     fun : Typeₙ → Typeₙ → Typeₙ
--     all : Kind → Typeₙ → Typeₙ
--     lam : Kind → Typeₙ → Typeₙ

--   data Typeᵤ : Set where
--     var : Index → Typeᵤ
--     app : Typeᵤ → Typeₙ → Typeᵤ

-- open import Context Typeₙ

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

-- TypeCtxₙ : Set
-- TypeCtxₙ = Ctx Typeₙ

-- variable
--   Γₙ : TypeCtxₙ
--   τₙ : Typeₙ

-- normalizeType : Type → Typeₙ
-- normalizeType = {!   !}

-- denormalizeType : Typeₙ → Type
-- denormalizeType = {!   !}

-- normalizeTypeCtx : TypeCtx → TypeCtxₙ
-- normalizeTypeCtx = {!   !} 

-- denormalizeTypeCtx : TypeCtxₙ → TypeCtx
-- denormalizeTypeCtx = {!   !}

-- postulate
--   _[_]ₙ : Typeₙ → Typeₙ → Typeₙ
--   substTypingHereₙ : ∀ {Φ κ κ' τ τₛ} → κ ∷ Φ ⊢ₙ τ ∶ κ' → Φ ⊢ₙ τₛ ∶ κ → Φ ⊢ₙ τ [ τₛ ]ₙ ∶ κ'

-- infix 3 _,_⊢_∶ₙ_
-- data _,_⊢_∶ₙ_ (Δ : KindCtx) (Γₙ : TypeCtxₙ) : Term → Typeₙ → Set where
--   var : ∀ {x τₙ}
--     → Δ ⊢ₙ τₙ ∶ ⋆
--     → Γₙ ∋ x ↦ τₙ
--     → Δ , Γₙ ⊢ var x ∶ₙ τₙ
--   lam : ∀ {τ τₙ τₙ' t}
--     → Δ ⊢ₙ fun τₙ τₙ' ∶ ⋆
--     → Δ ⊢ₙ τₙ ∶ ⋆
--     → Δ , τₙ ∷ Γₙ ⊢ t ∶ₙ τₙ'
--     → Δ , Γₙ ⊢ lam τ t ∶ₙ fun (normalizeType τ) τₙ'
--   app : ∀ {τₙ τₙ' t t'}
--     → Δ ⊢ₙ τₙ' ∶ ⋆
--     → Δ , Γₙ ⊢ t ∶ₙ fun τₙ τₙ'
--     → Δ , Γₙ ⊢ t' ∶ₙ τₙ
--     → Δ , Γₙ ⊢ app t t' ∶ₙ τₙ'
--   tlam : ∀ {κ τₙ t}
--     → Δ ⊢ₙ all κ τₙ ∶ ⋆
--     → κ ∷ Δ , Γₙ ⊢ t ∶ₙ τₙ
--     → Δ , Γₙ ⊢ tlam κ t ∶ₙ all κ τₙ
--   tapp : ∀ {κ τₙ t τₛ}
--     → Δ ⊢ₙ τₙ [ normalizeType τₛ ]ₙ ∶ ⋆
--     → Δ , Γₙ ⊢ t ∶ₙ all κ τₙ
--     → Δ ⊢ₙ normalizeType τₛ ∶ κ
--     → Δ , Γₙ ⊢ tapp t τₛ ∶ₙ τₙ [ normalizeType τₛ ]ₙ

-- -- renameTypeᵤ-id : ∀ {Φ J} (A : Φ ⊢ᵤ J) → renameTypeᵤ id A ≡ A
-- -- renameTypeᵤ-comp : ∀ {Φ Ψ Θ}{ρ : Renaming Φ Ψ} {ρ' : Renaming Ψ Θ} {J} (A : Φ ⊢ᵤ J)
-- --                  → renameTypeᵤ (ρ' ◦ ρ) A ≡ renameTypeᵤ ρ' (renameTypeᵤ ρ A)


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


-- lemma : WN τ → Δ ⊢ₙ normalizeType τ ∶ κ
-- lemma = {!   !} -- WN τ → wn τ → Δ ⊢ₙ normalizeType τ ∶ κ


-- normalizeKinding : Δ ⊢ τ ∶ κ → Δ ⊢ₙ normalizeType τ ∶ κ
-- normalizeKinding prf = lemma (normalization prf)

-- normalizeTyping : Δ , Γ ⊢ e ∶ τ → Δ , normalizeTypeCtx Γ ⊢ e ∶ₙ normalizeType τ 
-- normalizeTyping = {!   !}

-- denormalizeTyping : Δ , Γₙ ⊢ e ∶ₙ τₙ → Δ , denormalizeTypeCtx Γₙ ⊢ e ∶ denormalizeType τₙ
-- denormalizeTyping = {!   !}