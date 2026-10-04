open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Vec using ([]; _∷_)
open import Syntax
open import Typing

module Semantics where

data Value {m n : Nat} : Term m n → Set where
  lam : ∀ {τ t} → Value (lam τ t)
  tlam : ∀ {κ t} → Value (tlam κ t)


data _⇒_ {m n} : Term m n → Term m n → Set where