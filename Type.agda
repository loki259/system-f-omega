module Type where

open import Prelude

open import Kind public


-- τ := α | τ → τ | λ (α : κ) . τ | τ τ | ∀ (α : κ) . τ
data Type : Set where
  var : Index → Type
  fun : Type → Type → Type
  lam : Kind → Type → Type
  app : Type → Type → Type
  all : Kind → Type → Type

variable
  τ τ' τ₁ τ₁' τ₂ τ₂' τₛ : Type