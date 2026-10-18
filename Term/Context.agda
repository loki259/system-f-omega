module Term.Context where

open import Term

open import Context Type public
open import Type.Context public using (KindCtx; Δ; Δ'; Δ'')


TypeCtx : Set
TypeCtx = Ctx Type

variable
  Γ Γ' : TypeCtx