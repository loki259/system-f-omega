open import Agda.Builtin.Nat public using (Nat; suc; zero)
open import Data.Bool public
open import Data.List public using (List; []; _∷_; lookup; map)
open import Relation.Nullary.Decidable public hiding (map)
open import Data.Product public hiding (map) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality public