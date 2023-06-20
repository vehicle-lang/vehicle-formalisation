
module MiniVehicle.LossFunctions.FailedInstantiation1 where

-- Tries to use the domain (-∞ , ∞) unsuccessfully and illustrates
-- the problems that occur with negation around zero and with
-- strict inequalities.

open import Data.Sum as Sum
open import Data.Product as Prod
open import Data.Rational
open import Data.Rational.Properties
open import Data.Bool hiding (_≤_; _<_; _<?_; _≤?_) renaming (Bool to 𝔹; T to True)
open import Data.Bool.Properties using (T?; not-involutive)
open import Function
open import Function.Reasoning
open import Relation.Nullary
open import Relation.Unary using (Decidable)
open import Relation.Binary.PropositionalEquality using (cong)

open import Util
open import MiniVehicle.Language.StandardSemantics
open import MiniVehicle.LossFunctions.GenericDifferentiableLogic

open DifferentiableLogic
open ⇔-Reasoning

private
  variable
    a b : 𝔹
    p q r : ℚ

postulate p≤r×q≤r⇔p⊔q≤r : (p ≤ r × q ≤ r) ⇔ p ⊔ q ≤ r
postulate p≤r⊎q≤r⇔p⊓q≤r : (p ≤ r ⊎ q ≤ r) ⇔ p ⊓ q ≤ r

logic : DifferentiableLogic
logic .⟪Bool⟫ = ℚ
logic ._⟪and⟫_ = _⊔_
logic ._⟪or⟫_ = _⊓_
logic .⟪not⟫ = -_
logic ._⟪≤⟫_ = _-_
logic ._⟪<⟫_ = _-_

Truish : ℚ → Set
Truish = _≤ 0ℚ

Truish? : Decidable Truish
Truish? = _≤? 0ℚ

⟪and⟫-⇿ : ∀ p q → (Truish p × Truish q) ⇔ (Truish (p ⊔ q))
⟪and⟫-⇿ p q = p≤r×q≤r⇔p⊔q≤r

⟪or⟫-⇿ : ∀ p q → (Truish p ⊎ Truish q) ⇔ (Truish (p ⊓ q))
⟪or⟫-⇿ p q = p≤r⊎q≤r⇔p⊓q≤r

⟪not⟫-⇿ : ∀ p → Truish p ⇔ (¬ (Truish (- p)))
⟪not⟫-⇿ p = begin
  p ≤ 0ℚ             ⇔⟨ {!!} ⟩     -- PROBLEM
  p < 0ℚ             ⇔⟨ {!!} ⟩
  - p > 0ℚ           ⇔⟨ {!!} ⟩
  (¬ (- p ≤ 0ℚ))     ∎

⟪≤⟫-⇿ : ∀ p q → True (p ≤ᵇ q) ⇔ Truish (p - q)
⟪≤⟫-⇿ p q = begin
  True (p ≤ᵇ q) ⇔⟨ ≤ᵇ⇔≤ ⟩
  p ≤ q         ⇔⟨ p≤q⇔p-q≤0 ⟩
  p - q ≤ 0ℚ    ∎

⟪<⟫-⇿ : ∀ p q → True (p <ᵇ q) ⇔ Truish (p - q)
⟪<⟫-⇿ p q = begin
  True (p <ᵇ q) ⇔⟨ <ᵇ⇔< ⟩
  p < q         ⇔⟨ {!!} ⟩ -- PROBLEM
  p - q ≤ 0ℚ    ∎
  
valid : DifferentiableLogicRelation logic
valid = predicateToRelation logic $ record
  { Truish = Truish
  ; Truish? = Truish?
  ; ⟪and⟫-⇿ = ⟪and⟫-⇿
  ; ⟪or⟫-⇿ = ⟪or⟫-⇿
  ; ⟪not⟫-⇿ = ⟪not⟫-⇿
  ; ⟪≤⟫-⇿ = ⟪≤⟫-⇿
  ; ⟪<⟫-⇿ = {!!}
  }
