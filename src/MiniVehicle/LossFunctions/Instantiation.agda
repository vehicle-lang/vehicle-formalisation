
module MiniVehicle.LossFunctions.Instantiation where

open import Data.Sum as Sum
open import Data.Product as Prod
open import Data.Rational
open import Data.Rational.Properties
open import Data.Bool hiding (_≤_; _<_; _<?_; _≤?_) renaming (Bool to 𝔹; T to True)
open import Data.Bool.Properties hiding (_<?_; _≤?_)
open import Data.Empty using (⊥-elim)
open import Algebra
open import Function
open import Function.Reasoning
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (cong)
open import Relation.Unary using (Decidable)

open import Util
open import MiniVehicle.Language.StandardSemantics
open import MiniVehicle.LossFunctions.GenericDifferentiableLogic

open DifferentiableLogic
open ⇔-Reasoning

------------------------------------------------------------------------------
-- Define the set of non-negative rationals and operations over them.

ℚ⁺ : Set
ℚ⁺ = Σ ℚ NonNegative

max⁺ : Op₂ ℚ⁺
max⁺ (p , p⁺) (q , q⁺) = p ⊔ q , ⊔-pres-nonNegative p⁺ q⁺

min⁺ : Op₂ ℚ⁺
min⁺ (p , p⁺) (q , q⁺) = p ⊓ q , ⊓-pres-nonNegative p⁺ q⁺

------------------------------------------------------------------------------
-- Define the sum type of two non-negative rationals. One of which represents
-- truthiness and one which reprsents falsiness.

data ℚ² : Set where
  truth : (p : ℚ⁺) → ℚ²
  falsity : (p : ℚ⁺) → ℚ²

_⟦and⟧_ : ℚ² → ℚ² → ℚ²
truth x ⟦and⟧ truth y = truth (max⁺ x y)
truth x ⟦and⟧ falsity y = falsity y
falsity x ⟦and⟧ truth y = falsity x
falsity x ⟦and⟧ falsity y = falsity (min⁺ x y)

_⟦or⟧_ : ℚ² → ℚ² → ℚ²
truth x ⟦or⟧ truth y = truth (min⁺ x y)
truth x ⟦or⟧ falsity y = truth y
falsity x ⟦or⟧ truth y = truth x
falsity x ⟦or⟧ falsity y = falsity (max⁺ x y)

⟦not⟧_ : ℚ² → ℚ²
⟦not⟧ truth   x = falsity x
⟦not⟧ falsity x = truth x

_⟦≤⟧_ : ℚ → ℚ → ℚ²
x ⟦≤⟧ y with x ≤? y
... | yes x≤y = truth (y - x , nonNegative (p≥q⇒p-q≥0 x≤y))
... | no  x≰y = falsity (x - y , nonNegative (p≥q⇒p-q≥0 (≰⇒≥ x≰y)))

logic : DifferentiableLogic
logic .⟪Bool⟫ = ℚ²
logic ._⟪and⟫_ = _⟦and⟧_
logic ._⟪or⟫_ = _⟦or⟧_
logic .⟪not⟫ = ⟦not⟧_
logic ._⟪≤⟫_ = _⟦≤⟧_

------------------------------------------------------------------------------
-- Correctness

private
  variable
    a b : 𝔹
    p q r : ℚ²

data Truish : ℚ² → Set where
  truth : ∀ q → Truish (truth q)

Truish? : Decidable Truish
Truish? (truth p) = yes (truth p)
Truish? (falsity p) = no λ()

⟪and⟫-⇿ : ∀ p q → (Truish p × Truish q) ⇔ (Truish (p ⟦and⟧ q))
⟪and⟫-⇿ (truth p) (truth q) = mk⇔ (λ _ → truth (max⁺ p q)) (λ _ → truth p , truth q)
⟪and⟫-⇿ (truth p) (falsity q) = mk⇔ (λ()) (λ())
⟪and⟫-⇿ (falsity p) (truth q) = mk⇔ (λ()) (λ())
⟪and⟫-⇿ (falsity p) (falsity q) = mk⇔ (λ()) (λ())

⟪or⟫-⇿ : ∀ p q → (Truish p ⊎ Truish q) ⇔ (Truish (p ⟦or⟧ q))
⟪or⟫-⇿ (truth p) (truth q) = mk⇔ (λ _ → truth (min⁺ p q)) (λ _ → inj₁ (truth p))
⟪or⟫-⇿ (truth p) (falsity q) = mk⇔ (λ _ → truth q) (λ _ → inj₁ (truth p))
⟪or⟫-⇿ (falsity p) (truth q) = mk⇔ (λ _ → truth p) (λ _ → inj₂ (truth q))
⟪or⟫-⇿ (falsity p) (falsity q) = mk⇔ (λ {(inj₁ ()); (inj₂ ())}) (λ())

⟪not⟫-⇿ : ∀ p → Truish p ⇔ (¬ (Truish (⟦not⟧ p)))
⟪not⟫-⇿ (truth p)   = mk⇔ (λ _ ()) (λ _ → truth p)
⟪not⟫-⇿ (falsity p) = mk⇔ (λ()) (λ f → ⊥-elim (f (truth p)))

⟪≤⟫-⇿ : ∀ p q → True (p ≤ᵇ q) ⇔ Truish (p ⟦≤⟧ q)
⟪≤⟫-⇿ p q with p ≤? q
... | yes p≤q = mk⇔ (λ p≤ᵇq → truth _) (λ _ → ≤⇒≤ᵇ p≤q)
... | no  p≰q = mk⇔ (λ p≤ᵇq → ⊥-elim (p≰q (≤ᵇ⇒≤ p≤ᵇq))) λ()

valid : ValidDifferentiableLogic logic
valid = record
  { Truish = Truish
  ; Truish? = Truish?
  ; ⟪and⟫-⇿ = ⟪and⟫-⇿
  ; ⟪or⟫-⇿ = ⟪or⟫-⇿
  ; ⟪not⟫-⇿ = ⟪not⟫-⇿
  ; ⟪≤⟫-⇿ = ⟪≤⟫-⇿
  }
