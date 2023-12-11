
module MiniVehicle.LossFunctions.GenericDifferentiableLogic where

open import Algebra.Core
open import Data.Rational as ℚ
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Data.Bool renaming (Bool to 𝔹; T to True; T? to True?)
open import Data.Bool.Properties using (not-involutive; T-∧; T-∨)
open import Function
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Decidable)
open import Relation.Binary.PropositionalEquality using (cong)

open import MiniVehicle.Language.StandardSemantics
open import Util

------------------------------------------------------------------------------
-- Definition

-- The set of operations the logic needs to implement.
record DifferentiableLogic : Set₁ where
  field
    ⟪Bool⟫ : Set
    _⟪and⟫_ : Op₂ ⟪Bool⟫
    _⟪or⟫_ : Op₂ ⟪Bool⟫
    ⟪not⟫ : Op₁ ⟪Bool⟫
    _⟪≤⟫_ : ℚ → ℚ → ⟪Bool⟫
    _⟪<⟫_ : ℚ → ℚ → ⟪Bool⟫

------------------------------------------------------------------------------
-- Correctness

module _ (dl : DifferentiableLogic) where
  open DifferentiableLogic dl

  private
    variable
      a b : 𝔹
      r s : ℚ
      p q : ⟪Bool⟫

  -- The most general conditions that we need for the proof of
  -- correctness for the entire language to go through.
  record DifferentiableLogicRelation  : Set₁ where
    field
      R : 𝔹 → ⟪Bool⟫ → Set
      R⟪and⟫ : R a p → R b q → R (a ∧ b) (p ⟪and⟫ q)
      R⟪or⟫ : R a p → R b q → R (a ∨ b) (p ⟪or⟫ q)
      R⟪not⟫ : R a p → R (not a) (⟪not⟫ p)
      R⟪≤⟫ : R (r ≤ᵇ s) (r ⟪≤⟫ s)
      R⟪<⟫ : R (r <ᵇ s) (r ⟪<⟫ s)


  -- A more narrow definition of correctness, using a predicate
  -- instead of relation which is sometimes simpler to construct.
  record DifferentiableLogicPredicate : Set₁ where
    field
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

  -- The predicate version can be used to construct the relation version
  predicateToRelation : DifferentiableLogicPredicate → DifferentiableLogicRelation
  predicateToRelation pred = record
    { R      = _⇿_
    ; R⟪and⟫ = λ {a} {p} {b} {q} a⇿p b⇿q → begin
      True (a ∧ b)          ⇔⟨ T-∧ ⟩
      (True a × True b)     ⇔⟨ a⇿p ×-⇔ b⇿q ⟩
      (Truish p × Truish q) ⇔⟨ ⟪and⟫-⇿ p q ⟩
      Truish (p ⟪and⟫ q)    ∎
    ; R⟪or⟫  = λ {a} {p} {b} {q} a⇿p b⇿q → begin
      True (a ∨ b)          ⇔⟨ T-∨ ⟩
      (True a ⊎ True b)     ⇔⟨ a⇿p ⊎-⇔ b⇿q ⟩
      (Truish p ⊎ Truish q) ⇔⟨ ⟪or⟫-⇿ p q ⟩
      Truish (p ⟪or⟫ q)     ∎
    ; R⟪not⟫ = λ {a} {p} a⇿p →
      ¬?-⇔ (True? (not a)) (Truish? (⟪not⟫ p)) $
        begin
          ¬ (True (not a))       ⇔⟨ True-not-⇔ ⟩
          True (not (not a))     ≡⟨ cong True (not-involutive a) ⟩
          True a                 ⇔⟨ a⇿p ⟩
          Truish p               ⇔⟨ ⟪not⟫-⇿ p ⟩
          (¬ (Truish (⟪not⟫ p))) ∎
    ; R⟪≤⟫   = λ {r} {s} → ⟪≤⟫-⇿ r s
    ; R⟪<⟫   = λ {r} {s} → ⟪<⟫-⇿ r s
    }
    where
    open DifferentiableLogicPredicate pred
    open ⇔-Reasoning
