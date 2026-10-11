module Context (A : Set) where

open import Prelude


private variable
  a b : A


--------------------------------------------------------------------------------
-- Syntax
--------------------------------------------------------------------------------

Ctx : Set → Set
Ctx = List

private variable
  Ψ Φ : Ctx A

IndexRenaming : Set
IndexRenaming = Nat → Nat

variable
  f : IndexRenaming

liftIndexRenaming : IndexRenaming → IndexRenaming
liftIndexRenaming f zero    = zero
liftIndexRenaming f (suc x) = suc (f x)


--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

data _∋_↦_ : ∀ {A} → Ctx A → Index → A → Set where
  here  : (a ∷ Ψ) ∋ zero ↦ a
  there : Ψ ∋ x ↦ a → (b ∷ Ψ) ∋ suc x ↦ a


uniq-∋ : Ψ ∋ x ↦ a → Ψ ∋ x ↦ b → a ≡ b
uniq-∋ here         here         = refl
uniq-∋ (there prf₁) (there prf₂) = uniq-∋ prf₁ prf₂


lookup : (Ψ : Ctx A) → Ψ ∋ x ↦ a → A
lookup (a ∷ Ψ) here        = a
lookup (_ ∷ Ψ) (there prf) = lookup Ψ prf

find : (Ψ : Ctx A) → (x : Index) → Dec (∃[ a ] Ψ ∋ x ↦ a)
find []      x    = no λ ()
find (x ∷ _) zero = yes ⟨ x , here ⟩
find (_ ∷ ψ) (suc x') with find ψ x'
... | no ref          = no λ { ⟨ a , there prf ⟩ → ref ⟨ a , prf ⟩ }
... | yes ⟨ a , prf ⟩ = yes ⟨ a , there prf ⟩


Renaming : Ctx A → Ctx A → IndexRenaming → Set
Renaming Φ Ψ f = ∀ {x a} → Φ ∋ x ↦ a → Ψ ∋ f x ↦ a

liftRenaming : Renaming Φ Ψ f → ∀ {a'} → Renaming (a' ∷ Φ) (a' ∷ Ψ) (liftIndexRenaming f)
liftRenaming ρ here        = here
liftRenaming ρ (there prf) = there (ρ prf)