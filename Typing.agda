open import Prelude
open import Syntax


module Typing where


Ctx : (T : Set) → Set
Ctx = List

TypeCtx : Set
TypeCtx = Ctx Kind

TermCtx : Set
TermCtx = Ctx Type

variable
  Δ : TypeCtx
  Γ : TermCtx

data _∋_↦_ : TypeCtx → Nat → Kind → Set where
  here  : (κ ∷ Δ) ∋ zero ↦ κ
  there : {x : Nat} {κ' : Kind} → Δ ∋ x ↦ κ → (κ' ∷ Δ) ∋ suc x ↦ κ

infix 3 _⊢_∶_
data _⊢_∶_ (Δ : TypeCtx) : Type → Kind → Set where
  var : ∀ {x κ} → Δ ∋ x ↦ κ → Δ ⊢ var x ∶ κ
  fun : ∀ {τ τ'} → Δ ⊢ τ ∶ ⋆ → Δ ⊢ τ' ∶ ⋆ → Δ ⊢ fun τ τ' ∶ ⋆
  all : ∀ {κ τ} → κ ∷ Δ ⊢ τ ∶ ⋆ → Δ ⊢ all κ τ ∶ ⋆
  lam : ∀ {κ κ' τ} → κ ∷ Δ ⊢ τ ∶ κ' → Δ ⊢ lam κ τ ∶ tfun κ κ'
  app : ∀ {τ τ' κ κ'} → Δ ⊢ τ ∶ tfun κ κ' → Δ ⊢ τ' ∶ κ → Δ ⊢ app τ τ' ∶ κ'


-- dom≡ : ∀ {A A' B B'} → fun A B ≡ fun A' B' → A ≡ A'
-- dom≡ refl = refl

-- rng≡ : ∀ {A A' B B'} → fun A B ≡ fun A' B' → B ≡ B'
-- rng≡ refl = refl

-- uniq-∋ : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
-- uniq-∋ Z Z                 =  refl
-- uniq-∋ Z (S x≢y _)         =  contradiction refl x≢y
-- uniq-∋ (S x≢y _) Z         =  contradiction refl x≢y
-- uniq-∋ (S _ ∋x) (S _ ∋x′)  =  uniq-∋ ∋x ∋x′

-- uniq-↑ : ∀ {Δ M A B} → Δ ⊢ M ↑ A → Δ ⊢ M ↑ B → A ≡ B
-- uniq-↑ (⊢` ∋x) (⊢` ∋x′)      =  uniq-∋ ∋x ∋x′
-- uniq-↑ (⊢L · ⊢M) (⊢L′ · ⊢M′) =  rng≡ (uniq-↑ ⊢L ⊢L′)
-- uniq-↑ (⊢↓ ⊢M) (⊢↓ ⊢M′)      =  refl

-- ¬arg : ∀ {Δ A B L M} → Δ ⊢ L ∶ fun A B → ¬ Δ ⊢ M ∶ A → ¬ (∃[ B' ] Δ ⊢ app L M ∶ B')
-- ¬arg ⊢L ¬⊢M ⟨ B′ , ⊢L′ · ⊢M′ ⟩ rewrite dom≡ (uniq-↑ ⊢L ⊢L′) = ¬⊢M ⊢M′


checkKind : ∀ (Δ : TypeCtx) (τ : Type) (κ : Kind) → Dec (Δ ⊢ τ ∶ κ)
checkKind = {!   !}

inferKind : ∀ (Δ : TypeCtx) (τ : Type) → Dec (∃[ κ ] Δ ⊢ τ ∶ κ)
inferKind Δ (var x)     = {!   !} -- yes ⟨ lookup Δ x , var ⟩
inferKind Δ (fun τ₁ τ₂) = {!   !}
inferKind Δ (lam κ τ) with inferKind (κ ∷ Δ) τ
...                   | yes ⟨ κ' , prf ⟩ = yes ⟨ tfun κ κ' , lam prf ⟩
...                   | no ref           = no λ { ⟨ tfun κ κ' , lam prf ⟩ → ref ⟨ κ' , prf ⟩ }
inferKind Δ (app τ₁ τ₂) with inferKind Δ τ₁
...                     | no ref          = no λ { ⟨ κ' , app prf _ ⟩ → ref ⟨ tfun _ κ' , prf ⟩ }
...                     | yes ⟨ ⋆ , prf ⟩ = no λ { ⟨ κ , app prf _ ⟩ → {!   !} }
...                     | yes ⟨ tfun κ κ' , prf₁ ⟩ with checkKind Δ τ₂ κ
...                                              | yes prf₂ = yes ⟨ κ' , app prf₁ prf₂ ⟩
...                                              | no ref   = no λ { ⟨ κ , app _ prf ⟩ → {!   !} }
inferKind Δ (all κ τ) with inferKind (κ ∷ Δ) τ
...                   | no ref = no λ { ⟨ ⋆ , all prf ⟩ → ref ⟨ ⋆ , prf ⟩ }
...                   | yes ⟨ tfun κ κ' , prf ⟩ = no {!   !}
...                   | yes ⟨ ⋆ , prf ⟩ = yes ⟨ ⋆ , all prf ⟩


postulate
  weaken : TermCtx → TermCtx
  --                    τ        α.t            t[τ/α]
  instantiate : Type → Type → Type


-- infix 3 _≡ₜ_
-- data _≡ₜ_ {m} : Type m → Type m → Set where
--   refl  : ∀ {τ} → τ ≡ₜ τ
--   sym   : ∀ {τ τ'} → τ ≡ₜ τ' → τ' ≡ₜ τ
--   trans : ∀ {τ₁ τ₂ τ₃} → τ₁ ≡ₜ τ₂ → τ₂ ≡ₜ τ₃ → τ₁ ≡ₜ τ₃
--   fun   : ∀ {τ₁ τ₁' τ₂ τ₂'} → τ₁ ≡ₜ τ₁' → τ₂ ≡ₜ τ₂' → fun τ₁ τ₂ ≡ₜ fun τ₁' τ₂'
--   all   : ∀ {κ τ τ'} → τ ≡ₜ τ' → all κ τ ≡ₜ all κ τ'
--   lam   : ∀ {κ τ τ'} → τ ≡ₜ τ' → lam κ τ ≡ₜ lam κ τ'
--   app   : ∀ {τ₁ τ₁' τ₂ τ₂'} → τ₁ ≡ₜ τ₁' → τ₂ ≡ₜ τ₂' → app τ₁ τ₂ ≡ₜ app τ₁' τ₂'
--   beta  : ∀ {κ τ τ'} → app (lam κ τ) τ' ≡ₜ instantiate τ' τ

infix 3 _,_⊢_∶_
data _,_⊢_∶_ (Δ : TypeCtx) (Γ : TermCtx) : Term → Type → Set where
  var : ∀ {v}
    → Δ , Γ ⊢ var v ∶ {!   !} -- lookup Γ v
  lam : ∀ {τ τ' t}
    → Δ , (τ ∷ Γ) ⊢ t ∶ τ'
    → Δ ⊢ τ ∶ ⋆
    → Δ , Γ ⊢ lam τ t ∶ fun τ τ'
  app : ∀ {τ τ' t t'}
    → Δ , Γ ⊢ t ∶ fun τ τ'
    → Δ , Γ ⊢ t' ∶ τ
    → Δ , Γ ⊢ app t t' ∶ τ'
  tlam : ∀ {κ τ t}
    → κ ∷ Δ , weaken Γ ⊢ t ∶ τ
    → Δ , Γ ⊢ tlam κ t ∶ all κ τ
  tapp : ∀ {κ τ t τ'}
    → Δ , Γ ⊢ t ∶ all κ τ
    → Δ ⊢ τ' ∶ κ
    → Δ , Γ ⊢ tapp t τ' ∶ instantiate τ' τ
  -- type-eq : ∀ {t τ τ'}
  --   → Δ , Γ ⊢ t ∶ τ
  --   → τ ≡ₜ τ'
  --   → Δ , Γ ⊢ t ∶ τ'