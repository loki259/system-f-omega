module Syntax where

open import Prelude


Index : Set
Index = Nat

-- κ := * | κ → κ
data Kind : Set where
  ⋆    : Kind
  tfun : Kind → Kind → Kind

-- τ := α | τ → τ | λ (α : κ) . τ | τ τ | ∀ (α : κ) . τ
data Type : Set where
  var : Index → Type
  fun : Type → Type → Type
  lam : Kind → Type → Type
  app : Type → Type → Type
  all : Kind → Type → Type

-- e := x | λ (x : τ) . e | e e | Λ (α : κ) . e | e [τ]
data Term : Set where
  var  : Index → Term
  lam  : Type → Term → Term
  app  : Term → Term → Term
  tlam : Kind → Term → Term
  tapp : Term → Type → Term

variable
  κ κ' κ₁ κ₁' κ₂ κ₂' : Kind
  τ τ' τ₁ τ₁' τ₂ τ₂' : Type
  e t u : Term
  x i : Index