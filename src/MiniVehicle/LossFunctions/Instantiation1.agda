
module MiniVehicle.LossFunctions.Instantiation1 where

open import Data.Sum as Sum
open import Data.Product as Prod
open import Data.Rational
open import Data.Rational.Properties
open import Data.Bool hiding (_≤_; _<_; _<?_; _≤?_) renaming (Bool to 𝔹; T to True)
open import Data.Bool.Properties hiding (_<?_; _≤?_)
open import Function
open import Function.Reasoning
open import Relation.Nullary

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

Truish : ℚ → Set
Truish = _≤ 0ℚ

⟪and⟫-⇿ : (True a ⇔ Truish p) → (True b ⇔ Truish q) → True (a ∧ b) ⇔ Truish (p ⊔ q)
⟪and⟫-⇿ {a} {p} {b} {q} a⇿p b⇿q = begin
  True (a ∧ b)     ⇔˘⟨ True-∧-⇔ ⟩
  True a × True b  ⇔⟨ a⇿p ×-⇔ b⇿q ⟩
  p ≤ 0ℚ × q ≤ 0ℚ ⇔⟨ p≤r×q≤r⇔p⊔q≤r ⟩
  p ⊔ q ≤ 0ℚ      ∎

⟪or⟫-⇿ : (True a ⇔ Truish p) → (True b ⇔ Truish q) → True (a ∨ b) ⇔ Truish (p ⊓ q)
⟪or⟫-⇿ {a} {p} {b} {q} a⇿p b⇿q = begin
  True (a ∨ b)       ⇔˘⟨ True-∨-⇔ ⟩
  (True a ⊎ True b)  ⇔⟨ a⇿p ⊎-⇔ b⇿q ⟩
  (p ≤ 0ℚ ⊎ q ≤ 0ℚ) ⇔⟨ p≤r⊎q≤r⇔p⊓q≤r ⟩
  p ⊓ q ≤ 0ℚ         ∎

⟪not⟫-⇿ : (True a ⇔ Truish p) → True (not a) ⇔ Truish (- p)
⟪not⟫-⇿ {a} {p} a⇿p = ¬?-⇔ (T? (not a)) (- p ≤? 0ℚ) $ begin
  ¬ (True (not a))   ⇔⟨ True-not-⇔ ⟩
  True (not (not a)) ⇔⟨ {!!} ⟩
  True a             ⇔⟨ a⇿p ⟩
  p ≤ 0ℚ             ⇔⟨ {!!} ⟩     -- PROBLEM
  p < 0ℚ             ⇔⟨ {!!} ⟩
  - p > 0ℚ           ⇔⟨ {!!} ⟩
  - p ≰ 0ℚ           ∎

⟪≤⟫-⇿ : True (p ≤ᵇ q) ⇔ Truish (p - q)
⟪≤⟫-⇿ {p} {q} = begin
  True (p ≤ᵇ q) ⇔⟨ ≤ᵇ⇔≤ ⟩
  p ≤ q         ⇔⟨ p≤q⇔p-q≤0 ⟩
  p - q ≤ 0ℚ    ∎

valid : ValidDifferentiableLogic logic soundAndComplete
valid = record
  { Truish = Truish
  ; ⟪and⟫-⇿ = ⟪and⟫-⇿
  ; ⟪or⟫-⇿ = ⟪or⟫-⇿
  ; ⟪not⟫-⇿ = ⟪not⟫-⇿
  ; ⟪≤⟫-⇿ = λ {p} {q} → ⟪≤⟫-⇿ {p} {q}
  }
