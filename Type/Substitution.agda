module Type.Substitution where

open import Prelude
open import Type
open import Type.Context
open import Type.Kinding


weakenTypeAt : Index → Type → Type
weakenTypeAt xᵣ (var x)     = var (weakenIndexAt xᵣ x)
weakenTypeAt xᵣ (fun τ₁ τ₂) = fun (weakenTypeAt xᵣ τ₁) (weakenTypeAt xᵣ τ₂)
weakenTypeAt xᵣ (lam κ τ)   = lam κ (weakenTypeAt (suc xᵣ) τ)
weakenTypeAt xᵣ (app τ₁ τ₂) = app (weakenTypeAt xᵣ τ₁) (weakenTypeAt xᵣ τ₂)
weakenTypeAt xᵣ (all κ τ)   = all κ (weakenTypeAt (suc xᵣ) τ)


substType : Type → Index → Type → Type
substType (var x)     xₛ τₛ with x ≟ₓ xₛ
... | no ref   with ⟨ x' , _ ⟩ ← lemma-inequality-implies-weakening-exists ref = var x'
... | yes refl = τₛ
substType (fun τ₁ τ₂) xₛ τₛ = fun (substType τ₁ xₛ τₛ) (substType τ₂ xₛ τₛ)
substType (lam κ τ)   xₛ τₛ = lam κ (substType τ (suc xₛ) (weakenTypeAt zero τₛ))
substType (app τ₁ τ₂) xₛ τₛ = app (substType τ₁ xₛ τₛ) (substType τ₂ xₛ τₛ)
substType (all κ τ)   xₛ τₛ = all κ (substType τ (suc xₛ) (weakenTypeAt zero τₛ))


infix 5 _[_↦_]
_[_↦_] : Type → Index → Type → Type
_[_↦_] = substType


--------------------------------------------------------------------------------

weakenKinding : Δ \\ xᵣ ⊢ τ ∶ κ → Δ ⊢ weakenTypeAt xᵣ τ ∶ κ
weakenKinding (var pₓ)    = var (weakenIndexing pₓ)
weakenKinding (fun p₁ p₂) = fun (weakenKinding p₁) (weakenKinding p₂)
weakenKinding (all p)     = all (weakenKinding p)
weakenKinding (lam p)     = lam (weakenKinding p)
weakenKinding (app p₁ p₂) = app (weakenKinding p₁) (weakenKinding p₂)


substKinding : Δ ⊢ τ ∶ κ → Δ ∋ xₛ ↦ κₛ → Δ \\ xₛ ⊢ τₛ ∶ κₛ → Δ \\ xₛ ⊢ substType τ xₛ τₛ ∶ κ
substKinding {xₛ = xₛ} (var {x = x} pₓ) pₓₛ pₛ with x ≟ₓ xₛ
... | no ref   with ⟨ x' , refl ⟩ ← lemma-inequality-implies-weakening-exists ref = var (strengthenIndexing pₓ)
... | yes refl with refl ← lookupUniqueness pₓ pₓₛ = pₛ
substKinding (lam p)     pₓₛ pₛ = lam (substKinding p (there pₓₛ) (weakenKinding pₛ))
substKinding (app p₁ p₂) pₓₛ pₛ = app (substKinding p₁ pₓₛ pₛ) (substKinding p₂ pₓₛ pₛ)
substKinding (fun p₁ p₂) pₓₛ pₛ = fun (substKinding p₁ pₓₛ pₛ) (substKinding p₂ pₓₛ pₛ)
substKinding (all p)     pₓₛ pₛ = all (substKinding p (there pₓₛ) (weakenKinding pₛ))