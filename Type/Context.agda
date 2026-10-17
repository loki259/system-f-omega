module Type.Context where

open import Type
open import Context Kind public


KindCtx : Set
KindCtx = Ctx Kind

variable
  Δ Δ' Δ'' : KindCtx