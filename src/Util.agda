{-# OPTIONS --postfix-projections --safe #-}

module Util where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

is-true-or-false : ∀ b → (b ≡ true) ⊎ (b ≡ false)
is-true-or-false false = inj₂ refl
is-true-or-false true = inj₁ refl
