
module MiniVehicle.LossFunctions.GenericDifferentiableLogic where

open import Algebra.Core
open import Data.Rational as ℚ
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Data.Bool renaming (Bool to 𝔹; T to True)
open import Function
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Decidable)

open import MiniVehicle.Language.StandardSemantics
open import Util

record DifferentiableLogic : Set₁ where
  field
    ⟪Bool⟫ : Set
    _⟪and⟫_ : Op₂ ⟪Bool⟫
    _⟪or⟫_ : Op₂ ⟪Bool⟫
    ⟪not⟫ : Op₁ ⟪Bool⟫
    _⟪≤⟫_ : ℚ → ℚ → ⟪Bool⟫
    _⟪<⟫_ : ℚ → ℚ → ⟪Bool⟫


record ValidDifferentiableLogic (dl : DifferentiableLogic) : Set₁ where
  open DifferentiableLogic dl
  field
    -- Predicate defining which subset of the set ⟪Bool⟫ maps to true.
    Truish : ⟪Bool⟫ → Set
    Truish? : Decidable Truish

  infix 2 _⇿_
  _⇿_ : 𝔹 → ⟪Bool⟫ → Set
  b ⇿ q = True b ⇔ Truish q

  field
    ⟪and⟫-⇿ : ∀ p q → (Truish p × Truish q) ⇔ (Truish (p ⟪and⟫ q))
    ⟪or⟫-⇿ : ∀ p q → (Truish p ⊎ Truish q) ⇔ (Truish (p ⟪or⟫ q))
    ⟪not⟫-⇿ : ∀ p → Truish p ⇔ (¬ (Truish (⟪not⟫ p)))
    ⟪≤⟫-⇿ : ∀ p q → p ≤ᵇ q ⇿ p ⟪≤⟫ q
    ⟪<⟫-⇿ : ∀ p q → p <ᵇ q ⇿ p ⟪<⟫ q
