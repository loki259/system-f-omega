module Context (A : Set) where

open import Prelude


private variable
  a a' b : A


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


--------------------------------------------------------------------------------

infix 3 _∋_↦_
data _∋_↦_ : ∀ {A} → Ctx A → Index → A → Set where
  here  : (a ∷ Ψ) ∋ zero ↦ a
  there : Ψ ∋ x ↦ a → (b ∷ Ψ) ∋ suc x ↦ a


lookupUniqueness : Ψ ∋ x ↦ a → Ψ ∋ x ↦ b → a ≡ b
lookupUniqueness here         here         = refl
lookupUniqueness (there prf₁) (there prf₂) = lookupUniqueness prf₁ prf₂


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
weaken {a' = a'} = weakenN 1 {as = a' ∷ []}

dropN : (n : Nat) → ∀ {as : Vec A n} → appendN n as Φ ∋ n + x ↦ a → Φ ∋ x ↦ a
dropN zero    {as = []}     prf         = prf
dropN (suc n) {as = a ∷ as} (there prf) = dropN n {as = as} prf

drop : a' ∷ Φ ∋ suc x ↦ a → Φ ∋ x ↦ a
drop {a' = a'} = dropN 1 {as = a' ∷ []}

drop∘weaken-id : ∀ {n : Nat} {as : Vec A n} {prf : Φ ∋ x ↦ a} → dropN n {as = as} (weakenN n {as = as} prf) ≡ prf
drop∘weaken-id {n = zero}  {as = []}     = refl
drop∘weaken-id {n = suc n} {as = a ∷ as} = drop∘weaken-id {n = n}

weakenRetraction : RetractableRenaming Φ (a ∷ Φ) suc
weakenRetraction {a = a} = record { rename = weaken; retract = drop; retract∘rename-id = drop∘weaken-id {as = a ∷ []} }


--------------------------------------------------------------------------------

infixl 5 _\\_
_\\_ : Ctx A → Index → Ctx A
[]      \\ _       = []
(a ∷ Ψ) \\ zero    = Ψ
(a ∷ Ψ) \\ (suc x) = a ∷ (Ψ \\ x)

lemma-\\-∷-commutativity : (a ∷ Ψ) \\ suc x ≡ a ∷ (Ψ \\ x)
lemma-\\-∷-commutativity = refl

lemma-\\-commutativity : x < x' → Ψ \\ x \\ x' ≡ Ψ \\ suc x' \\ x
lemma-\\-commutativity                           {Ψ = []}    _       = refl
lemma-\\-commutativity {x = zero}  {x' = suc x'} {Ψ = a ∷ Ψ} _       = refl
lemma-\\-commutativity {x = suc x} {x' = suc x'} {Ψ = a ∷ Ψ} (s≤s p) = cong (a ∷_) (lemma-\\-commutativity {Ψ = Ψ} p)

lemma-\\-with-consecutive-indices : Ψ ∋ x ↦ a → Ψ ∋ suc x ↦ a → Ψ \\ x ≡ Ψ \\ suc x
lemma-\\-with-consecutive-indices here               (there here) = refl
lemma-\\-with-consecutive-indices (there {b = b} pₓ) (there pₛₓ)  = cong (b ∷_) (lemma-\\-with-consecutive-indices pₓ pₛₓ)


weakenIndexAt : Index → Index → Index
weakenIndexAt zero     x       = suc x
weakenIndexAt (suc _)  zero    = zero
weakenIndexAt (suc xᵣ) (suc x) = suc (weakenIndexAt xᵣ x)

lemma-inequality-implies-weakening-exists : x ≢ xᵣ → ∃[ x' ] x ≡ weakenIndexAt xᵣ x'
lemma-inequality-implies-weakening-exists {x = zero}  {xᵣ = zero}   ref with () ← ref refl
lemma-inequality-implies-weakening-exists {x = zero}  {xᵣ = suc xᵣ} ref = ⟨ zero , refl ⟩
lemma-inequality-implies-weakening-exists {x = suc x} {xᵣ = zero}   ref = ⟨ x , refl ⟩
lemma-inequality-implies-weakening-exists {x = suc x} {xᵣ = suc xᵣ} ref with x ≟ₓ xᵣ
... | no ref'  = Σ-map suc (cong suc) (lemma-inequality-implies-weakening-exists ref')
... | yes refl with () ← ref refl

lemma-weakening-implies-inequality : x ≡ weakenIndexAt xᵣ x' → x ≢ xᵣ
lemma-weakening-implies-inequality {x = zero}  {xᵣ = zero}                 ()
lemma-weakening-implies-inequality {x = zero}  {xᵣ = suc xᵣ}               _  = λ ()
lemma-weakening-implies-inequality {x = suc x} {xᵣ = zero}                 _  = λ ()
lemma-weakening-implies-inequality {x = suc x} {xᵣ = suc xᵣ} {x' = zero}   ()
lemma-weakening-implies-inequality {x = suc x} {xᵣ = suc xᵣ} {x' = suc x'} eq
  = λ eq' → lemma-weakening-implies-inequality {x = x} {xᵣ = xᵣ} {x' = x'} (cong pred eq) (cong pred eq')

lemma-\\-commutativity' : x ≤ x' → Ψ \\ x \\ x' ≡ Ψ \\ weakenIndexAt x x' \\ x
lemma-\\-commutativity'                           {Ψ = []}    _       = refl
lemma-\\-commutativity' {x = zero}                {Ψ = a ∷ Ψ} _       = refl
lemma-\\-commutativity' {x = suc x} {x' = suc x'} {Ψ = a ∷ Ψ} (s≤s p) = cong (a ∷_) (lemma-\\-commutativity' {Ψ = Ψ} p)

lemma-weakenIndexAt-with-consecutive-indices : weakenIndexAt (suc xᵣ) x ≢ xᵣ → Ψ ∋ xᵣ ↦ a → Ψ ∋ suc xᵣ ↦ a → weakenIndexAt xᵣ x ≡ weakenIndexAt (suc xᵣ) x
lemma-weakenIndexAt-with-consecutive-indices {x = zero} ref  here        (there here) with () ← ref refl
lemma-weakenIndexAt-with-consecutive-indices {x = suc x} _   here        (there here) = refl
lemma-weakenIndexAt-with-consecutive-indices {x = zero}  _   (there pₓᵣ) (there pₛₓᵣ) = refl
lemma-weakenIndexAt-with-consecutive-indices {x = suc x} ref (there pₓᵣ) (there pₛₓᵣ) = cong suc (lemma-weakenIndexAt-with-consecutive-indices (ref ∘ cong suc) pₓᵣ pₛₓᵣ)

lemma-weakenIndexAt-injectivity : weakenIndexAt xᵣ x ≡ weakenIndexAt xᵣ x' → x ≡ x'
lemma-weakenIndexAt-injectivity               {x = zero}  {x' = zero}   refl = refl
lemma-weakenIndexAt-injectivity {xᵣ = zero}   {x = zero}  {x' = suc x'} ()
lemma-weakenIndexAt-injectivity {xᵣ = suc xᵣ} {x = zero}  {x' = suc x'} ()
lemma-weakenIndexAt-injectivity {xᵣ = zero}   {x = suc x} {x' = zero}   ()
lemma-weakenIndexAt-injectivity {xᵣ = suc xᵣ} {x = suc x} {x' = zero}   ()
lemma-weakenIndexAt-injectivity {xᵣ = zero}   {x = suc x} {x' = suc x'} eq   = cong pred eq
lemma-weakenIndexAt-injectivity {xᵣ = suc xᵣ} {x = suc x} {x' = suc x'} eq   = cong suc (lemma-weakenIndexAt-injectivity (cong pred eq))

lemma-weakenIndexAt-identity : x ≤ xᵣ → weakenIndexAt (suc xᵣ) x ≡ x
lemma-weakenIndexAt-identity {x = zero}                _          = refl
lemma-weakenIndexAt-identity {x = suc x} {xᵣ = suc xᵣ} (s≤s x≤xᵣ) = cong suc (lemma-weakenIndexAt-identity x≤xᵣ)

lemma-weakenIndexAt-commutativity : Ψ ∋ x ↦ a → xᵣ ≤ xᵣ' → weakenIndexAt xᵣ (weakenIndexAt xᵣ' x) ≡ weakenIndexAt (suc xᵣ') (weakenIndexAt xᵣ x)
lemma-weakenIndexAt-commutativity here      z≤n       = refl
lemma-weakenIndexAt-commutativity here      (s≤s ≤-p) = refl
lemma-weakenIndexAt-commutativity (there p) z≤n       = refl
lemma-weakenIndexAt-commutativity (there p) (s≤s ≤-p) = cong suc (lemma-weakenIndexAt-commutativity p ≤-p)

-- lemma : weakenIndexAt (weakenIndexAt xᵣ xᵣ') (weakenIndexAt xᵣ x) ≡ weakenIndexAt (weakenIndexAt (weakenIndexAt xᵣ xᵣ') xᵣ) x' → weakenIndexAt xᵣ' x ≡ x'
-- lemma = {!   !}

-- lemma' : weakenIndexAt (weakenIndexAt xᵣ xᵣ') (weakenIndexAt xᵣ x) ≡ weakenIndexAt (weakenIndexAt (weakenIndexAt xᵣ xᵣ') xᵣ) (weakenIndexAt xᵣ' x)
-- lemma' = ?


--------------------------------------------------------------------------------

weakenIndexing : Ψ \\ xᵣ ∋ x ↦ a → Ψ ∋ weakenIndexAt xᵣ x ↦ a
weakenIndexing {Ψ = _ ∷ Ψ'} {xᵣ = zero}   p         = there p
weakenIndexing {Ψ = _ ∷ Ψ'} {xᵣ = suc xᵣ} here      = here
weakenIndexing {Ψ = _ ∷ Ψ'} {xᵣ = suc xᵣ} (there p) = there (weakenIndexing p)

weakenIndexingAt : (xᵣ : Index) → Ψ \\ xᵣ ∋ x ↦ a → Ψ ∋ weakenIndexAt xᵣ x ↦ a
weakenIndexingAt {Ψ = _ ∷ Ψ'} zero     p         = there p
weakenIndexingAt {Ψ = _ ∷ Ψ'} (suc xᵣ) here      = here
weakenIndexingAt {Ψ = _ ∷ Ψ'} (suc xᵣ) (there p) = there (weakenIndexingAt xᵣ p)

strengthenIndexing : Ψ ∋ weakenIndexAt xᵣ x ↦ a → Ψ \\ xᵣ ∋ x ↦ a
strengthenIndexing {xᵣ = zero}   {x = zero}  (there p) = p
strengthenIndexing {xᵣ = zero}   {x = suc x} (there p) = p
strengthenIndexing {xᵣ = suc _}  {x = zero}  here      = here
strengthenIndexing {xᵣ = suc xᵣ} {x = suc x} (there p) = there (strengthenIndexing {xᵣ = xᵣ} p)

strengthenIndexingAt : (xᵣ : Index) → Ψ ∋ weakenIndexAt xᵣ x ↦ a → Ψ \\ xᵣ ∋ x ↦ a
strengthenIndexingAt {x = zero}  zero     (there p) = p
strengthenIndexingAt {x = suc x} zero     (there p) = p
strengthenIndexingAt {x = zero}  (suc _)  here      = here
strengthenIndexingAt {x = suc x} (suc xᵣ) (there p) = there (strengthenIndexingAt xᵣ p)


-- data _⊢_↦_≡ₓ_↦_ (Ψ : Ctx A) : Index → A → Index → A → Set where
--   -- weakened : Ψ ∋ x ↦ a → Ψ \\ x ∋ x' ↦ a' → Ψ ⊢ x ↦ a ≡ₓ weakenIndex x x' ↦ a'
--   weakened : Ψ ⊢ x ↦ a ≡ₓ weakenIndex x x' ↦ a' → Ψ ⊢ x ↦ a ≡ₓ weakenIndex x x' ↦ a'
--   refl     : Ψ ∋ x ↦ a → Ψ ⊢ x ↦ a ≡ₓ x ↦ a

-- postulate checkIndexingEquality : Ψ ∋ x ↦ a → Ψ ∋ x' ↦ a' → Dec (x ≡ x' × a ≡ a')