open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Data.Fin.Base using (Fin)

module Syntax where

-- κ := * | κ → κ
data Kind : Set where
  ⋆    : Kind
  tfun : Kind → Kind → Kind

-- τ := α | τ → τ | λ (α : κ) . τ | τ τ | ∀ (α : κ) . τ
data Type (m : Nat) : Set where
  var : Fin m → Type m
  fun : Type m → Type m → Type m
  lam : Kind → Type (suc m) → Type m
  app : Type m → Type m → Type m
  all : Kind → Type (suc m) → Type m

-- e := x | λ (x : τ) . e | e e | Λ (α : κ) . e | e [τ]
data Term (m n : Nat) : Set where
  var  : Fin n → Term m n
  lam  : Type m → Term m (suc n) → Term m n
  app  : Term m n → Term m n → Term m n
  tlam : Kind → Term (suc m) n → Term m n
  tapp : Term m n → Type m → Term m n

variable
  κ : Kind
  τ : {m : Nat} → Type m
  e t : {m n : Nat} → Term m n