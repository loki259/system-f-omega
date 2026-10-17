{-# OPTIONS --allow-unsolved-metas #-}

module Context (A : Set) where

open import Prelude


private variable
  a a' b : A


--------------------------------------------------------------------------------
-- Syntax
--------------------------------------------------------------------------------

Ctx : Set → Set
Ctx = List

private variable
  Ψ Ψ' Φ Φ' : Ctx A

IndexRenaming : Set
IndexRenaming = Nat → Nat

variable
  r r' : IndexRenaming

liftIndexRenamingN : Nat → IndexRenaming → IndexRenaming
liftIndexRenamingN zero    r = r
liftIndexRenamingN (suc n) r zero    = zero
liftIndexRenamingN (suc n) r (suc x) = suc (liftIndexRenamingN n r x)

liftIndexRenaming : IndexRenaming → IndexRenaming
liftIndexRenaming = liftIndexRenamingN 1

lemma-contract-liftIndexRenaming : liftIndexRenamingN 1 (liftIndexRenamingN n r) ≡ liftIndexRenamingN (suc n) r
lemma-contract-liftIndexRenaming {zero } = refl
lemma-contract-liftIndexRenaming {suc n} = function-extensionality λ { {zero}  → refl; {suc n} → refl }

--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

infix 3 _∋_↦_
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
Renaming Φ Ψ r = ∀ {x a} → Φ ∋ x ↦ a → Ψ ∋ r x ↦ a

variable
  ρ : Renaming Φ Ψ r 

Renaming-∘ : {ctx₁ : Ctx A}
          → {ctx₂ : Ctx A}
          → {ctx₃ : Ctx A}
          → Renaming ctx₂ ctx₃ r'
          → Renaming ctx₁ ctx₂ r
          → Renaming ctx₁ ctx₃ (r' ∘ r)
Renaming-∘ ρ' ρ prf = ρ' (ρ prf)

appendN : (n : Nat) → Vec A n → Ctx A → Ctx A
appendN zero    []       Φ = Φ
appendN (suc n) (a ∷ as) Φ = a ∷ appendN n as Φ

liftRenamingN : (n : Nat) → ∀ {as : Vec A n} → Renaming Φ Ψ r → Renaming (appendN n as Φ) (appendN n as Ψ) (liftIndexRenamingN n r)
liftRenamingN zero    {as = []}     ρ = ρ
liftRenamingN (suc n) {as = a ∷ as} ρ = λ { here → here; (there prf) → there (liftRenamingN n ρ prf) }

liftRenaming : Renaming Φ Ψ r → Renaming (a ∷ Φ) (a ∷ Ψ) (liftIndexRenaming r)
liftRenaming {a = a} = liftRenamingN 1 {as = a ∷ []}

-- lemma-contract-liftRenaming : ∀ {n a} {as : Vec A n} → liftRenamingN 1 {as = a ∷ []} (liftRenamingN n {as = as} ρ) ≡ liftRenamingN (suc n) {as = a ∷ as} ρ
-- lemma-contract-liftRenaming = {!   !}

record RetractableRenaming (Φ : Ctx A) (Ψ : Ctx A) (r : IndexRenaming) : Set where
  field
    rename            : Renaming Φ Ψ r
    retract           : Ψ ∋ r x ↦ a → Φ ∋ x ↦ a
    retract∘rename-id : ∀ {prf : Φ ∋ x ↦ a} → retract (rename prf) ≡ prf
  
  lift : RetractableRenaming (a' ∷ Φ) (a' ∷ Ψ) (liftIndexRenaming r)
  lift .rename = liftRenaming (rename)
  lift .retract {x = zero}  here        = here
  lift .retract {x = suc _} (there prf) = there (retract prf)
  lift .retract∘rename-id {prf = here}                                            = refl
  lift .retract∘rename-id {prf = there prf} rewrite retract∘rename-id {prf = prf} = refl
open RetractableRenaming public

weakenN : (n : Nat) → ∀ {as : Vec A n} → Φ ∋ x ↦ a → appendN n as Φ ∋ n + x ↦ a 
weakenN zero    {as = []}     prf = prf
weakenN (suc n) {as = a ∷ as} prf = there (weakenN n {as = as} prf)

weaken : Φ ∋ x ↦ a → a' ∷ Φ ∋ suc x ↦ a
-- weaken prf = there prf
weaken {a' = a'} = weakenN 1 {as = a' ∷ []}

dropN : (n : Nat) → ∀ {as : Vec A n} → appendN n as Φ ∋ n + x ↦ a → Φ ∋ x ↦ a
dropN zero    {as = []}     prf         = prf
dropN (suc n) {as = a ∷ as} (there prf) = dropN n {as = as} prf

drop : a' ∷ Φ ∋ suc x ↦ a → Φ ∋ x ↦ a
-- drop (there prf) = prf
drop {a' = a'} = dropN 1 {as = a' ∷ []}

-- drop∘weaken-id : ∀ {prf : Φ ∋ x ↦ a} → drop {a' = a'} (weaken {a' = a'} prf) ≡ prf
drop∘weaken-id : ∀ {n : Nat} {as : Vec A n} {prf : Φ ∋ x ↦ a} → dropN n {as = as} (weakenN n {as = as} prf) ≡ prf
drop∘weaken-id {n = zero}  {as = []}     = refl
drop∘weaken-id {n = suc n} {as = a ∷ as} = drop∘weaken-id {n = n}

weakenRetraction : RetractableRenaming Φ (a ∷ Φ) suc
weakenRetraction {a = a} = record { rename = weaken; retract = drop; retract∘rename-id = drop∘weaken-id {as = a ∷ []} }