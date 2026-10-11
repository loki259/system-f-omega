module Term where

open import Prelude

open import Type public


-- e := x | λ (x : τ) . e | e e | Λ (α : κ) . e | e [τ]
data Term : Set where
  var  : Index → Term
  lam  : Type → Term → Term
  app  : Term → Term → Term
  tlam : Kind → Term → Term
  tapp : Term → Type → Term

variable
  e t u : Term