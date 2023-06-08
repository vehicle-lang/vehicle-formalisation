
module MiniVehicle.LossFunctions.GenericDifferentiableLogic where

open import Algebra.Core
open import Data.Rational as ℚ
open import Data.Bool renaming (Bool to 𝔹; T to True)
open import Function

open import MiniVehicle.Language.StandardSemantics

record DifferentiableLogic : Set₁ where
  field
    ⟪Bool⟫ : Set
    _⟪and⟫_ : Op₂ ⟪Bool⟫
    _⟪or⟫_ : Op₂ ⟪Bool⟫
    ⟪not⟫ : Op₁ ⟪Bool⟫
    _⟪≤⟫_ : ℚ → ℚ → ⟪Bool⟫


record ValidDifferentiableLogic (dl : DifferentiableLogic) (Rel : Relationship) : Set₁ where
  open DifferentiableLogic dl
  open Relationship Rel

  field
    -- Predicate defining which subset of the set ⟪Bool⟫ maps to true.
    Truish : ⟪Bool⟫ → Set

  infix 2 _⇿_
  _⇿_ : 𝔹 → ⟪Bool⟫ → Set
  b ⇿ q = R (True b) (Truish q)

  field
    ⟪and⟫-⇿ : ∀ {a b p q} → a ⇿ p → b ⇿ q → a ∧ b ⇿ p ⟪and⟫ q
    ⟪or⟫-⇿ : ∀ {a b p q} → a ⇿ p → b ⇿ q → a ∨ b ⇿ p ⟪or⟫ q
    ⟪not⟫-⇿ : ∀ {a p} → a ⇿ p → not a ⇿ ⟪not⟫ p
    ⟪≤⟫-⇿ : ∀ {p q} → p ≤ᵇ q ⇿ p ⟪≤⟫ q
