{-# OPTIONS --postfix-projections --safe #-}

module MiniVehicle.Qualifiers where

data LinearityVal : Set where
  const linear nonlinear : LinearityVal

data PolarityVal : Set where
  U Ex : PolarityVal

data MaxLinRel : LinearityVal → LinearityVal → LinearityVal → Set where
  const-const   : MaxLinRel const const const
  const-linear  : MaxLinRel const linear linear
  linear-const  : MaxLinRel linear const linear
  linear-linear : MaxLinRel linear linear linear

data MulRel : LinearityVal → LinearityVal → LinearityVal → Set where
  const-const  : MulRel const const const
  const-linear : MulRel const linear linear
  linear-const : MulRel linear const linear

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
