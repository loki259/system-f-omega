open import Syntax
open import Typing
open import Semantics

module Preservation where

preservation : ∀ {m n} {Δ : TypeCtx m} {Γ : TermCtx m n} {t t' τ}
  → Δ , Γ ⊢ t ∶ τ
  → t ⇒ t'
  → Δ , Γ ⊢ t' ∶ τ
preservation = {!   !}