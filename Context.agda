module Context where

open import Prelude

--------------------------------------------------------------------------------
-- Syntax
--------------------------------------------------------------------------------

Ctx : (T : Set) → Set
Ctx = List


IndexRenaming : Set
IndexRenaming = Nat → Nat

liftIndexRenaming : IndexRenaming → IndexRenaming
liftIndexRenaming f zero    = zero
liftIndexRenaming f (suc x) = suc (f x)

--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

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


Renaming : ∀ {A} → Ctx A → Ctx A → IndexRenaming → Set
Renaming {A} Φ Ψ f = ∀ {x a} → Φ ∋ x ↦ a → Ψ ∋ f x ↦ a

liftRenaming : ∀ {A Φ Ψ f} → Renaming {A} Φ Ψ f → ∀ {a'} → Renaming {A} (a' ∷ Φ) (a' ∷ Ψ) (liftIndexRenaming f)
liftRenaming ρ here        = here
liftRenaming ρ (there prf) = there (ρ prf)