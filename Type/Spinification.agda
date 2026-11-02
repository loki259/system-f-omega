module Type.Spinification where

open import Prelude
open import Type hiding (τₛ)
open import Type.Context
open import Type.Kinding
open import Type.SpineForm renaming (⟨_⟩_ to app)
open import Type.SpineForm.Kinding renaming (⟨_⟩_ to app)


spinifyType : Type → Typeₛ
spinifyType (var x)     = app (var x) []
spinifyType (fun τ₁ τ₂) = app (fun (spinifyType τ₁) (spinifyType τ₂)) []
spinifyType (lam κ τ)   = app (lam κ (spinifyType τ)) []
spinifyType (all κ τ)   = app (all κ (spinifyType τ)) []
spinifyType (app τ₁ τ₂) with app τₕ τs ← spinifyType τ₁
  = app τₕ (appendToSpine τs (spinifyType τ₂))

lemma-allTypesSpinifyToSpineApp : ∃[ τₕ ] ∃[ τs ] spinifyType τ ≡ app τₕ τs
lemma-allTypesSpinifyToSpineApp {var x}     = ⟨ var x , ⟨ [] , refl ⟩ ⟩
lemma-allTypesSpinifyToSpineApp {fun τ₁ τ₂} = ⟨ fun (spinifyType τ₁) (spinifyType τ₂) , ⟨ [] , refl ⟩ ⟩
lemma-allTypesSpinifyToSpineApp {lam κ τ}   = ⟨ lam κ (spinifyType τ) , ⟨ [] , refl ⟩ ⟩
lemma-allTypesSpinifyToSpineApp {all κ τ}   = ⟨ all κ (spinifyType τ) , ⟨ [] , refl ⟩ ⟩
lemma-allTypesSpinifyToSpineApp {app τ₁ τ₂}
  with τ₁' ← spinifyType τ₁ | ⟨ τₕ , ⟨ τs , refl ⟩ ⟩ ← lemma-allTypesSpinifyToSpineApp {τ = τ₁}
  = ⟨ τₕ , ⟨ appendToSpine τs (spinifyType τ₂) , refl ⟩ ⟩

spinifyKinding : Δ ⊢ τ ∶ κ → Δ ⊢ₛ spinifyType τ ∶ κ
spinifyKinding (var pₓ)    = app (var pₓ) []
spinifyKinding (fun p₁ p₂) = app (fun (spinifyKinding p₁) (spinifyKinding p₂)) []
spinifyKinding (all p)     = app (all (spinifyKinding p)) []
spinifyKinding (lam p)     = app (lam (spinifyKinding p)) []
spinifyKinding (app {τ₁ = τ₁} p₁ p₂) with p₁' ← spinifyKinding p₁
  rewrite lemma-allTypesSpinifyToSpineApp {τ = τ₁} .proj₂ .proj₂ 
  with app pₕ ps ← p₁' = app pₕ (appendToKindingSpine ps (spinifyKinding p₂))


--------------------------------------------------------------------------------

mutual
  despinifyTypeₛ : Typeₛ → Type
  despinifyTypeₛ (app τₕ τs) = foldSpine (despinifyTypeₕ τₕ) τs
  
  despinifyTypeₕ : Typeₕ → Type
  despinifyTypeₕ (var x)     = var x
  despinifyTypeₕ (fun τ₁ τ₂) = fun (despinifyTypeₛ τ₁) (despinifyTypeₛ τ₂)
  despinifyTypeₕ (lam κ τ)   = lam κ (despinifyTypeₛ τ)
  despinifyTypeₕ (all κ τ)   = all κ (despinifyTypeₛ τ)
  
  foldSpine : Type → Spine → Type
  foldSpine τ []        = τ
  foldSpine τ (τₛ ∷ τs) = foldSpine (app τ (despinifyTypeₛ τₛ)) τs

mutual
  despinifyKindingₛ : Δ ⊢ₛ τₛ ∶ κ → Δ ⊢ despinifyTypeₛ τₛ ∶ κ
  despinifyKindingₛ (app pₕ ps) = foldKindingSpine (despinifyKindingₕ pₕ) ps

  despinifyKindingₕ : Δ ⊢ₕ τₕ ∶ κ → Δ ⊢ despinifyTypeₕ τₕ ∶ κ
  despinifyKindingₕ (var pₓ)    = var pₓ
  despinifyKindingₕ (fun p₁ p₂) = fun (despinifyKindingₛ p₁) (despinifyKindingₛ p₂)
  despinifyKindingₕ (lam p)     = lam (despinifyKindingₛ p)
  despinifyKindingₕ (all p)     = all (despinifyKindingₛ p)

  foldKindingSpine : Δ ⊢ τ ∶ κ → Δ ∣ κ ⊢ₛ τs ∶ κ' → Δ ⊢ foldSpine τ τs ∶ κ'
  foldKindingSpine p []        = p
  foldKindingSpine p (pₛ ∷ ps) = foldKindingSpine (app p (despinifyKindingₛ pₛ)) ps