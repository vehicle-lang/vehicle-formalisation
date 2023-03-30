{-# OPTIONS --safe --postfix-projections #-}

module KindTheory where

open import Data.List

record Signature : Set₁ where
  field
    sort   : Set

    op     : Set
    opSort : op → sort
    opArgs : op → List sort

    type   : Set
    tyArgs : type → List sort

-- Each “sort” gets interpreted as a Setoid, and each operation as a
-- setoid morphism

-- Each
