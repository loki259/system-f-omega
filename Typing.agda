open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Data.Vec using (Vec; []; _∷_; lookup; map)
open import Syntax

module Typing where

Ctx : (T : Set) → Nat → Set
Ctx = Vec

TypeCtx : Nat → Set
TypeCtx = Ctx Kind

TermCtx : Nat → Nat → Set
TermCtx m = Ctx (Type m)

variable
  Δ : {m : Nat} → TypeCtx m
  Γ : {m n : Nat} → TermCtx m n

infix 3 _⊢_∶_
data _⊢_∶_ {m} (Δ : TypeCtx m) : Type m → Kind → Set where
  var : ∀ {v} → Δ ⊢ var v ∶ lookup Δ v
  fun : ∀ {τ τ'} → Δ ⊢ τ ∶ ⋆ → Δ ⊢ τ' ∶ ⋆ → Δ ⊢ fun τ τ' ∶ ⋆
  all : ∀ {κ τ} → κ ∷ Δ ⊢ τ ∶ ⋆ → Δ ⊢ all κ τ ∶ ⋆
  lam : ∀ {κ κ' τ} → κ ∷ Δ ⊢ τ ∶ κ' → Δ ⊢ lam κ τ ∶ tfun κ κ'
  app : ∀ {τ τ' κ κ'} → Δ ⊢ τ ∶ tfun κ κ' → Δ ⊢ τ' ∶ κ → Δ ⊢ app τ τ' ∶ κ'


-- data _≡ₜ_

-- infix 3 _≡ₜ_

postulate
  weaken : ∀ {m n} → TermCtx m n → TermCtx (suc m) n
  --                                      τ     α.t         t[τ/α]
  instantiate : ∀ {n} → Type n → Type (suc n) → Type n

infix 3 _,_⊢_∶_
data _,_⊢_∶_ {m n} (Δ : TypeCtx m) (Γ : TermCtx m n) : Term m n → Type m → Set where
  var : ∀ {v}
    → Δ , Γ ⊢ var v ∶ lookup Γ v
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