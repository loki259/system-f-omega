open import Data.Nat using (zero)
open import Data.Vec using ([])
open import Data.Product using (Σ)
open import Data.Sum using (_⊎_)
open import Syntax
open import Typing
open import Semantics

module Progress where

progress : ∀ {m Δ τ} (t : Term m zero)
  → Δ , [] ⊢ t ∶ τ
  → Value t ⊎ Σ (Term m zero) (λ t' → t ⇒ t')
progress = {!   !}