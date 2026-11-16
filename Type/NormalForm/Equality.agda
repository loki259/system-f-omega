module Type.NormalForm.Equality where

open import Prelude
open import Type.Context
open import Type.NormalForm
open import Type.NormalForm.Kinding

infix 3 _⊢ₙ_≡ₜ_∶_
data _⊢ₙ_≡ₜ_∶_ (Δ : KindCtx) : Typeₙ → Typeₙ → Kind → Set where
  refl : Δ ⊢ₙ τₙ ∶ κ → Δ ⊢ₙ τₙ ≡ₜ τₙ ∶ κ

≡ₜ-symₙ : Δ ⊢ₙ τₙ ≡ₜ τₙ' ∶ κ → Δ ⊢ₙ τₙ' ≡ₜ τₙ ∶ κ
≡ₜ-symₙ (refl p) = refl p

≡ₜ-transₙ : Δ ⊢ₙ τₙ ≡ₜ τₙ' ∶ κ → Δ ⊢ₙ τₙ' ≡ₜ τₙ'' ∶ κ → Δ ⊢ₙ τₙ ≡ₜ τₙ'' ∶ κ
≡ₜ-transₙ (refl p) (refl _) = refl p

extract≡ : Δ ⊢ₙ τₙ ≡ₜ τₙ' ∶ κ → τₙ ≡ τₙ'
extract≡ (refl _) = refl


infix 3 _⊢ᵤ_≡ₜ_∶_
data _⊢ᵤ_≡ₜ_∶_ (Δ : KindCtx) : Typeᵤ → Typeᵤ → Kind → Set where
  refl : Δ ⊢ᵤ τᵤ ∶ κ → Δ ⊢ᵤ τᵤ ≡ₜ τᵤ ∶ κ


infix 3 _∣_⊢ₙ_≡ₜ_∶_
data _∣_⊢ₙ_≡ₜ_∶_ (Δ : KindCtx) (κ : Kind) : Spineₙ → Spineₙ → Kind → Set where
  refl : Δ ∣ κ ⊢ₙ τs ∶ κ' → Δ ∣ κ ⊢ₙ τs ≡ₜ τs ∶ κ'

extract≡fromSpineEq : Δ ∣ κ ⊢ₙ τs ≡ₜ τs' ∶ κ' → τs ≡ τs'
extract≡fromSpineEq (refl _) = refl