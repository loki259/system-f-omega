module Term.Context where

open import Term
open import Context Type

open import Type.Context public hiding (Ctx)


TypeCtx : Set
TypeCtx = Ctx Type

variable
  Γ Γ' : TypeCtx