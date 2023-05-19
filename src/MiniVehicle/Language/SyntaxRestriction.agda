{-# OPTIONS --safe #-}

module MiniVehicle.Language.SyntaxRestriction where

open import Data.Unit
open import Relation.Binary.Definitions

open import Util

------------------------------------------------------------------------------
-- Restriction type

-- This record type is used to instantiate restrictions on the syntax of
-- MiniVehicle depending on the appropriate backend targeted. For example,
-- the verifier backend can only handle linear expressions with
-- non-alternating quantifiers.
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

record _⊆ᵣ_ (S R : SyntaxRestriction) : Set where
  private
    module R = SyntaxRestriction S
    module S = SyntaxRestriction R

  field
    toₙ : S.NumRestriction → R.NumRestriction
    toₙ-const : toₙ Pres₁ S.NumConstRestriction ⟶ R.NumConstRestriction
    toₙ-func : toₙ Pres₂ S.FuncRestriction ⟶ R.FuncRestriction
    toₙ-add : toₙ Pres₃ S.AddRestriction ⟶ R.AddRestriction
    toₙ-mul : toₙ Pres₃ S.MulRestriction ⟶ R.MulRestriction

    toᵇ : S.BoolRestriction → R.BoolRestriction
    toᵇ-const : toᵇ Pres₁ S.BoolConstRestriction ⟶ R.BoolConstRestriction
    {-
    BoolConstRestriction : BoolRestriction → Set
    NotRestriction : BoolRestriction → BoolRestriction → Set
    AndRestriction : BoolRestriction → BoolRestriction → BoolRestriction → Set
    OrRestriction : BoolRestriction → BoolRestriction → BoolRestriction → Set
    LeqRestriction : NumRestriction → NumRestriction → BoolRestriction → Set
    QuantRestriction : NumRestriction → BoolRestriction → BoolRestriction → Set
    IfRestriction : BoolRestriction → Set
    -}
------------------------------------------------------------------------------
-- Restriction type

data PolarityVal : Set where
  U Ex : PolarityVal

data ConstPolRel : PolarityVal → Set where
  U : ConstPolRel U

data MaxPolRel : PolarityVal → PolarityVal → PolarityVal → Set where
  U-U   : MaxPolRel U U U
  U-Ex  : MaxPolRel U Ex Ex
  Ex-U  : MaxPolRel Ex U Ex
  Ex-Ex : MaxPolRel Ex Ex Ex

data NegPolRel : PolarityVal → PolarityVal → Set where
  U  : NegPolRel U U

data QuantifyRel : PolarityVal → PolarityVal → Set where
  U  : QuantifyRel U Ex
  Ex : QuantifyRel Ex Ex

------------------------------------------------------------------------------
-- The default restriction

-- As Agda is constructive we can't easily represent the standard semantics
-- of `Bool`. Therefore we track the standard polarity of an expression.
defaultRestriction : SyntaxRestriction
defaultRestriction = record
  { NumRestriction      = ⊤
  ; NumConstRestriction = λ _ → ⊤
  ; FuncRestriction = λ _ _ → ⊤
  ; AddRestriction = λ _ _ _ → ⊤
  ; MulRestriction = λ _ _ _ → ⊤
  ; BoolRestriction = PolarityVal
  ; BoolConstRestriction = ConstPolRel
  ; NotRestriction = NegPolRel
  ; AndRestriction = MaxPolRel
  ; OrRestriction = MaxPolRel
  ; LeqRestriction = λ _ _ → ConstPolRel
  ; QuantRestriction = λ _ → QuantifyRel
  ; IfRestriction = ConstPolRel
  }
