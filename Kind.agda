module Kind where

open import Prelude


-- κ := * | κ → κ
infixr 6 _⇒_
data Kind : Set where
  ⋆   : Kind
  _⇒_ : Kind → Kind → Kind

variable
  κ κ' κ'' κ₁ κ₁' κ₂ κ₂' : Kind


⇒-inj : κ₁ ⇒ κ₂ ≡ κ₁' ⇒ κ₂' → κ₁ ≡ κ₁' × κ₂ ≡ κ₂'
⇒-inj refl = ⟨ refl , refl ⟩


infix 5 _≟ₖ_
_≟ₖ_ : (κ : Kind) → (κ' : Kind) → Dec (κ ≡ κ')
⋆        ≟ₖ ⋆     = yes refl
⋆        ≟ₖ _ ⇒ _ = no λ ()
_ ⇒ _    ≟ₖ ⋆     = no λ ()
κ₁ ⇒ κ₁' ≟ₖ κ₂ ⇒ κ₂' with κ₁ ≟ₖ κ₂ | κ₁' ≟ₖ κ₂'
... | yes prf | yes prf' = yes (cong₂ _⇒_ prf prf')
... | yes prf | no  ref  = no λ { prf* → ref (⇒-inj prf* .proj₂) }
... | no  ref | yes prf  = no λ { prf* → ref (⇒-inj prf* .proj₁) }
... | no  ref | no  ref' = no λ { prf* → ref (⇒-inj prf* .proj₁) }