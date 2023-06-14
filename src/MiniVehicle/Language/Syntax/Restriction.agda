{-# OPTIONS --safe #-}

module MiniVehicle.Language.Syntax.Restriction where

open import Data.Unit
open import Relation.Binary.Definitions

open import Util

------------------------------------------------------------------------------
-- Restriction type

-- This record type is used to instantiate restrictions on the syntax of
-- MiniVehicle depending on the appropriate backend targeted. For example,
-- the verifier backend can only handle linear expressions with
-- non-alternating quantifiers.
record Restriction : Set₁ where
  field
    NumRestriction       : Set
    NumConstRestriction  : NumRestriction → Set
    FuncRestriction      : NumRestriction → NumRestriction → Set
    AddRestriction       : NumRestriction → NumRestriction → NumRestriction → Set
    MulRestriction       : NumRestriction → NumRestriction → NumRestriction → Set

    BoolRestriction      : Set
    BoolConstRestriction : BoolRestriction → Set
    NotRestriction       : BoolRestriction → BoolRestriction → Set
    AndRestriction       : BoolRestriction → BoolRestriction → BoolRestriction → Set
    OrRestriction        : BoolRestriction → BoolRestriction → BoolRestriction → Set
    CompRestriction      : NumRestriction → NumRestriction → BoolRestriction → Set
    QuantRestriction     : NumRestriction → BoolRestriction → BoolRestriction → Set
    IfRestriction        : BoolRestriction → Set

------------------------------------------------------------------------------
-- Encoding of polarities to track the quantification status of a Bools

data PolarityVal         : Set where
  U Ex                   : PolarityVal

data ConstPolRel         : PolarityVal → Set where
  U                      : ConstPolRel U

data MaxPolRel           : PolarityVal → PolarityVal → PolarityVal → Set where
  U-U                    : MaxPolRel U U U
  U-Ex                   : MaxPolRel U Ex Ex
  Ex-U                   : MaxPolRel Ex U Ex
  Ex-Ex                  : MaxPolRel Ex Ex Ex

data NegPolRel           : PolarityVal → PolarityVal → Set where
  U                      : NegPolRel U U

data QuantifyRel         : PolarityVal → PolarityVal → Set where
  U                      : QuantifyRel U Ex
  Ex                     : QuantifyRel Ex Ex

------------------------------------------------------------------------------
-- The default restriction

-- As Agda is constructive we can't easily represent the standard semantics
-- of expressions of type `Bool` containing quantifiers. Therefore we use the
-- default restriction to track the standard polarity of the boolean type,
-- which then allows us to assign separate semantics for quantified vs
-- non-quantified Boolean expressions.
--
-- This doesn't actually impose any restrictions on the syntax apart from in
-- the case of `if` whose condition must be an unquantified boolean.
defaultRestriction       : Restriction
defaultRestriction = record
  { NumRestriction       = ⊤
  ; NumConstRestriction  = λ _ → ⊤
  ; FuncRestriction      = λ _ _ → ⊤
  ; AddRestriction       = λ _ _ _ → ⊤
  ; MulRestriction       = λ _ _ _ → ⊤
  ; BoolRestriction      = PolarityVal
  ; BoolConstRestriction = ConstPolRel
  ; NotRestriction       = NegPolRel
  ; AndRestriction       = MaxPolRel
  ; OrRestriction        = MaxPolRel
  ; CompRestriction      = λ _ _ → ConstPolRel
  ; QuantRestriction     = λ _ → QuantifyRel
  ; IfRestriction        = ConstPolRel
  }
