{-# OPTIONS --allow-unsolved-metas #-}

module Prelude where

open import Agda.Builtin.Nat public using (Nat; suc; zero)
open import Data.Bool public
open import Data.List public using (List; []; _∷_; map)
open import Relation.Nullary.Decidable public hiding (map)
open import Data.Product public renaming (_,_ to ⟨_,_⟩; map to Σ-map; zip to Σ-zip; map₁ to Σ-map₁; map₂ to Σ-map₂)
open import Relation.Binary.PropositionalEquality public hiding ([_])
open import Relation.Nullary.Negation public using (¬_)

case_of_ : ∀ {A B : Set} → A → (A → B) → B
case x of f = f x