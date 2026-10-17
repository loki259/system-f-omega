module Kind where

-- κ := * | κ → κ
data Kind : Set where
  ⋆    : Kind
  tfun : Kind → Kind → Kind

variable
  κ κ' κ'' κ₁ κ₁' κ₂ κ₂' : Kind