module Syntax where

open import Prelude


-- κ := * | κ → κ
data Kind : Set where
  ⋆    : Kind
  tfun : Kind → Kind → Kind

-- τ := α | τ → τ | λ (α : κ) . τ | τ τ | ∀ (α : κ) . τ
data Type : Set where
  var : Nat → Type
  fun : Type → Type → Type
  lam : Kind → Type → Type
  app : Type → Type → Type
  all : Kind → Type → Type

mutual
  data Typeₙ : Set where
    neu : Typeᵤ → Typeₙ
    fun : Typeₙ → Typeₙ → Typeₙ
    all : Kind → Typeₙ → Typeₙ
    lam : Kind → Typeₙ → Typeₙ

  data Typeᵤ : Set where
    var : Nat → Typeᵤ
    app : Typeᵤ → Typeₙ → Typeᵤ

-- e := x | λ (x : τ) . e | e e | Λ (α : κ) . e | e [τ]
data Term : Set where
  var  : Nat → Term
  lam  : Type → Term → Term
  app  : Term → Term → Term
  tlam : Kind → Term → Term
  tapp : Term → Type → Term

variable
  κ : Kind
  τ : Type
  e t : Term