module Context where

open import Prelude


Ctx : (T : Set) → Set
Ctx = List

data _∋_↦_ {A : Set} : Ctx A → Nat → A → Set where
  here  : ∀ {ctx a} → (a ∷ ctx) ∋ zero ↦ a
  there : ∀ {ctx x a b} → ctx ∋ x ↦ a → (b ∷ ctx) ∋ suc x ↦ a


uniq-∋ : ∀ {A x a b} {ctx : Ctx A} → ctx ∋ x ↦ a → ctx ∋ x ↦ b → a ≡ b
uniq-∋ here         here         = refl
uniq-∋ (there prf₁) (there prf₂) = uniq-∋ prf₁ prf₂


lookup : ∀ {A x a} → (ctx : Ctx A) → ctx ∋ x ↦ a → A
lookup (a ∷ ctx) here        = a
lookup (_ ∷ ctx) (there prf) = lookup ctx prf

find : ∀ {A} → (ctx : Ctx A) → (x : Nat) → Dec (∃[ a ] ctx ∋ x ↦ a)
find []        x    = no λ ()
find (x ∷ ctx) zero = yes ⟨ x , here ⟩
find (x ∷ ctx) (suc x') with find ctx x'
... | no ref          = no λ { ⟨ a , there prf ⟩ → ref ⟨ a , prf ⟩}
... | yes ⟨ a , prf ⟩ = yes ⟨ a , there prf ⟩


Renaming : ∀ {A} → Ctx A → Ctx A → Set
Renaming Φ Ψ = ∀ {x a} → Φ ∋ x ↦ a → ∃[ x' ] Ψ ∋ x' ↦ a

lift : ∀ {A Φ Ψ} → Renaming {A} Φ Ψ → ∀ {a} → Renaming (a ∷ Φ) (a ∷ Ψ)
lift ρ here        = ⟨ zero , here ⟩         -- Leave newly bound variable untouched
lift ρ (there prf) = Σ-map suc there (ρ prf) -- Apply renaming to other variables and add 1