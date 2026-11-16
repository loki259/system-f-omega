module Prelude where

open import Data.Nat public
  using (suc; zero; _≟_; _+_; _∸_; _≤_; z≤n; s≤s; _<_; z<s; s<s; pred) renaming (ℕ to Nat)
open import Data.Nat.Properties public using (≤-reflexive)
open import Data.List public
  using (List; []; _∷_; map; length; _++_; _∷ʳ_)
open import Data.Vec public
  using (Vec; []; _∷_)
open import Relation.Nullary.Decidable public
  renaming (map to dec-map)
open import Data.Product public
  renaming (_,_ to ⟨_,_⟩; map to Σ-map; zip to Σ-zip; map₁ to Σ-map₁; map₂ to Σ-map₂)
open import Relation.Binary.PropositionalEquality public
  hiding ([_])
open import Relation.Nullary.Negation public
  using (¬_)
open import Function.Base public


Index : Set
Index = Nat

variable
  m m' n n' : Nat
  x x' xᵣ xᵣ' xₛ xₛ' : Index

infix 5 _≟ₓ_
_≟ₓ_ : (x : Index) → (x' : Index) → Dec (x ≡ x')
_≟ₓ_ = _≟_


postulate function-extensionality : ∀ {A B : Set} {f f' : A → B} → (∀ {a : A} → f a ≡ f' a) → f ≡ f'