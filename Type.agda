module Type where

open import Prelude

open import Kind public


-- τ := α | τ → τ | λ (α : κ) . τ | τ τ | ∀ (α : κ) . τ
data Type : Set where
  var : Index → Type
  fun : Type → Type → Type
  lam : Kind → Type → Type
  app : Type → Type → Type
  all : Kind → Type → Type

variable
  τ τ' τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' τₛ : Type


var-inj : ∀ {x x' : Index} → var x ≡ var x' → x ≡ x'
var-inj refl = refl

fun-inj : fun τ₁ τ₂ ≡ fun τ₁' τ₂' → τ₁ ≡ τ₁' × τ₂ ≡ τ₂'
fun-inj refl = ⟨ refl , refl ⟩

app-inj : app τ₁ τ₂ ≡ app τ₁' τ₂' → τ₁ ≡ τ₁' × τ₂ ≡ τ₂'
app-inj refl = ⟨ refl , refl ⟩

lam-inj : lam κ τ ≡ lam κ' τ' → κ ≡ κ' × τ ≡ τ'
lam-inj refl = ⟨ refl , refl ⟩

all-inj : all κ τ ≡ all κ' τ' → κ ≡ κ' × τ ≡ τ'
all-inj refl = ⟨ refl , refl ⟩


infix 5 _≟ₜ_
_≟ₜ_ : (τ : Type) → (τ' : Type) → Dec (τ ≡ τ')
var x ≟ₜ var x' with x ≟ x'
... | yes prf = yes (cong var prf)
... | no ref  = no λ { prf → ref (var-inj prf) }
var _ ≟ₜ fun _ _ = no λ ()
var _ ≟ₜ lam _ _ = no λ ()
var _ ≟ₜ app _ _ = no λ ()
var _ ≟ₜ all _ _ = no λ ()
fun _ _ ≟ₜ var _ = no λ ()
fun τ₁ τ₂ ≟ₜ fun τ₁' τ₂' with τ₁ ≟ₜ τ₁' | τ₂ ≟ₜ τ₂'
... | yes prf | yes prf' = yes (cong₂ fun prf prf')
... | yes prf | no  ref  = no λ { prf* → ref (fun-inj prf* .proj₂) }
... | no  ref | yes prf' = no λ { prf* → ref (fun-inj prf* .proj₁) }
... | no  ref | no  ref' = no λ { prf* → ref (fun-inj prf* .proj₁) }
fun _ _ ≟ₜ lam _ _ = no λ ()
fun _ _ ≟ₜ app _ _ = no λ ()
fun _ _ ≟ₜ all _ _ = no λ ()
lam _ _ ≟ₜ var _   = no λ ()
lam _ _ ≟ₜ fun _ _ = no λ ()
lam κ τ ≟ₜ lam κ' τ' with κ ≟ₖ κ' | τ ≟ₜ τ'
... | yes prf | yes prf' = yes (cong₂ lam prf prf')
... | yes prf | no  ref  = no λ { prf* → ref (lam-inj prf* .proj₂) }
... | no  ref | yes prf' = no λ { prf* → ref (lam-inj prf* .proj₁) }
... | no  ref | no  ref' = no λ { prf* → ref (lam-inj prf* .proj₁) }
lam _ _ ≟ₜ app _ _ = no λ ()
lam _ _ ≟ₜ all _ _ = no λ ()
app _ _ ≟ₜ var _   = no λ ()
app _ _ ≟ₜ fun _ _ = no λ ()
app _ _ ≟ₜ lam _ _ = no λ ()
app τ₁ τ₂ ≟ₜ app τ₁' τ₂' with τ₁ ≟ₜ τ₁' | τ₂ ≟ₜ τ₂'
... | yes prf | yes prf' = yes (cong₂ app prf prf')
... | yes prf | no  ref  = no λ { prf* → ref (app-inj prf* .proj₂) }
... | no  ref | yes prf' = no λ { prf* → ref (app-inj prf* .proj₁) }
... | no  ref | no  ref' = no λ { prf* → ref (app-inj prf* .proj₁) }
app _ _ ≟ₜ all _ _ = no λ ()
all _ _ ≟ₜ var _   = no λ ()
all _ _ ≟ₜ fun _ _ = no λ ()
all _ _ ≟ₜ lam _ _ = no λ ()
all _ _ ≟ₜ app _ _ = no λ ()
all κ τ ≟ₜ all κ' τ' with κ ≟ₖ κ' | τ ≟ₜ τ'
... | yes prf | yes prf' = yes (cong₂ all prf prf')
... | yes prf | no  ref  = no λ { prf* → ref (all-inj prf* .proj₂) }
... | no  ref | yes prf' = no λ { prf* → ref (all-inj prf* .proj₁) }
... | no  ref | no  ref' = no λ { prf* → ref (all-inj prf* .proj₁) }