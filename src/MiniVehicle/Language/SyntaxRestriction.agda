{-# OPTIONS --safe #-}

module MiniVehicle.Language.SyntaxRestriction where

open import Data.Unit

-- This record type is used to instantiate restrictions on the syntax of mini-vehicle
-- depending on the appropriate backend targeted. For example, the verifier backend
-- can only handle linear expressions with non-alternating quantifiers.
record SyntaxRestriction : Set₁ where
  field
    NumRestriction : Set
    NumConstRestriction : NumRestriction → Set
    FuncRestriction : NumRestriction → NumRestriction → Set
    AddRestriction : NumRestriction → NumRestriction → NumRestriction → Set
    MulRestriction : NumRestriction → NumRestriction → NumRestriction → Set

    BoolRestriction : Set
    BoolConstRestriction : BoolRestriction → Set
    NotRestriction : BoolRestriction → BoolRestriction → Set
    AndRestriction : BoolRestriction → BoolRestriction → BoolRestriction → Set
    OrRestriction : BoolRestriction → BoolRestriction → BoolRestriction → Set
    LeqRestriction : NumRestriction → NumRestriction → BoolRestriction → Set
    QuantRestriction : NumRestriction → BoolRestriction → BoolRestriction → Set
    IfRestriction : BoolRestriction → Set


-- No restrictions on syntax
noRestriction : SyntaxRestriction
noRestriction = record
  { NumRestriction      = ⊤
  ; NumConstRestriction = λ _ → ⊤
  ; FuncRestriction = λ _ _ → ⊤
  ; AddRestriction = λ _ _ _ → ⊤
  ; MulRestriction = λ _ _ _ → ⊤
  ; BoolRestriction = ⊤
  ; BoolConstRestriction = λ _ → ⊤
  ; NotRestriction = λ _ _ → ⊤
  ; AndRestriction = λ _ _ _ → ⊤
  ; OrRestriction = λ _ _ _ → ⊤
  ; LeqRestriction = λ _ _ _ → ⊤
  ; QuantRestriction = λ _ _ _ → ⊤
  ; IfRestriction = λ _ → ⊤
  }
