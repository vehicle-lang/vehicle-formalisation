{-# OPTIONS --postfix-projections --safe #-}

module MiniVehicle.Restriction where

-- This record type is used to instatiate restrictions on the syntax of mini-vehicle
-- depending on the appropriate backend targetted. For example, the verifier backend
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
