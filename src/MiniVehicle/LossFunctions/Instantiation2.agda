
module MiniVehicle.LossFunctions.Instantiation2 where

open import Data.Sum as Sum
open import Data.Product as Prod
open import Data.Rational hiding (truncate)
open import Data.Rational.Properties
open import Data.Bool hiding (_≤_; _<_; _<?_; _≤?_) renaming (Bool to 𝔹; T to True)
open import Data.Bool.Properties hiding (_<?_; _≤?_)
open import Data.Integer using (+_)
open import Data.Empty using (⊥-elim)
open import Algebra
open import Function
open import Function.Reasoning
open import Relation.Nullary hiding (True)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong; cong₂; refl; subst)
open import Relation.Unary using (Decidable)
open import Relation.Nullary.Negation

open import Util
open import Util.PositiveRational

open import MiniVehicle.Language.StandardSemantics
open import MiniVehicle.LossFunctions.GenericDifferentiableLogic

open DifferentiableLogic

------------------------------------------------------------------------------
-- Define the signed non-negative rationals.

⟦Bool⟧ : Set
⟦Bool⟧  = ℚ⁺ × ℚ⁺

_⟦and⟧_ : Op₂ ⟦Bool⟧ 
(x₊ , x₋) ⟦and⟧ (y₊ , y₋) = min⁺ x₊ y₊ , max⁺ x₋ y₋

_⟦or⟧_ : Op₂ ⟦Bool⟧ 
(x₊ , x₋) ⟦or⟧ (y₊ , y₋) = min⁺ x₊ y₊ , max⁺ x₋ y₋

⟦not⟧_ : Op₁ ⟦Bool⟧ 
⟦not⟧ (x₊ , x₋) = x₋ , x₊

_⟦≤⟧_ : ℚ → ℚ → ⟦Bool⟧
x ⟦≤⟧ y with x ≤? y
... | yes x≤y = (y - x [ x≤y ] , 0ℚ⁺)
... | no  x≰y = (0ℚ⁺ , x - y [ ≰⇒≥ x≰y ])

_⟦<⟧_ : ℚ → ℚ → ⟦Bool⟧ 
x ⟦<⟧ y with x <? y
... | yes x<y = (y - x [ <⇒≤ x<y ] , 0ℚ⁺)
... | no  x≮y = (0ℚ⁺ , x - y [ ≮⇒≥ x≮y ])

logic : DifferentiableLogic
logic .⟪Bool⟫ = ⟦Bool⟧ 
logic ._⟪and⟫_ = _⟦and⟧_
logic ._⟪or⟫_ = _⟦or⟧_
logic .⟪not⟫ = ⟦not⟧_
logic ._⟪≤⟫_ = _⟦≤⟧_
logic ._⟪<⟫_ = _⟦<⟧_

------------------------------------------------------------------------------
-- Correctness

private
  variable
    a b : 𝔹
    r s : ℚ
    p q : ⟦Bool⟧

data R : 𝔹 → ⟦Bool⟧ → Set where
  truthy : ∀ (p : ℚ⁺) → R true (p , 0ℚ⁺)
  falsey : ∀ (p : ℚ⁺) → R false (0ℚ⁺ , p)

R⟪and⟫ : R a p → R b q → R (a ∧ b) (p ⟦and⟧ q)
R⟪and⟫ (truthy p) (truthy q) = subst (R true) (sym (cong₂ _,_ refl (max⁺-identityʳ 0ℚ⁺))) (truthy (min⁺ p q))
R⟪and⟫ (truthy p) (falsey q) = subst (R false) (sym (cong₂ _,_ (min⁺-zeroʳ p) (max⁺-identityˡ q))) (falsey q)
R⟪and⟫ (falsey p) (truthy q) = subst (R false) (sym (cong₂ _,_ (min⁺-zeroˡ q) (max⁺-identityʳ p))) (falsey p)
R⟪and⟫ (falsey p) (falsey q) = subst (R false) (sym (cong₂ _,_ (min⁺-identityʳ 0ℚ⁺) refl)) (falsey (max⁺ p q))

R⟪or⟫ : R a p → R b q → R (a ∨ b) (p ⟦or⟧ q)
R⟪or⟫ (truthy p) (truthy q) = subst (R true) (sym (cong₂ _,_ refl (max⁺-identityʳ 0ℚ⁺))) (truthy (min⁺ p q))
R⟪or⟫ (truthy p) (falsey q) = subst (R true) (sym (cong₂ _,_ (min⁺-identityʳ p) (max⁺-zeroˡ q))) (truthy p)
R⟪or⟫ (falsey p) (truthy q) = subst (R true) (sym (cong₂ _,_ (min⁺-identityˡ q) (max⁺-zeroʳ p))) (truthy q)
R⟪or⟫ (falsey p) (falsey q) = subst (R false) (sym (cong₂ _,_ (min⁺-identityʳ 0ℚ⁺) refl)) (falsey (max⁺ p q))

R⟪not⟫ : R a p → R (not a) (⟦not⟧ p)
R⟪not⟫ (truthy p) = falsey p
R⟪not⟫ (falsey p) = truthy p

R⟪≤⟫ : ∀ {p q} → R (p ≤ᵇ q) (p ⟦≤⟧ q)
R⟪≤⟫ {p} {q} with p ≤? q
... | yes p≤q rewrite True⇒true (≤⇒≤ᵇ p≤q) = truthy (q - p [ p≤q ])
... | no  p≰q rewrite False⇒false (contraposition ≤ᵇ⇒≤ p≰q) = falsey (p - q [ ≰⇒≥ p≰q ])

R⟪<⟫ : ∀ {p q} → R (p <ᵇ q) (p ⟦<⟧ q)
R⟪<⟫ {p} {q} with p <? q
... | yes p<q rewrite True⇒true (<⇒<ᵇ p<q) = truthy (q - p [ <⇒≤ p<q ])
... | no  p≮q rewrite False⇒false (contraposition <ᵇ⇒< p≮q) = falsey (p - q [ ≮⇒≥ p≮q ])

valid : DifferentiableLogicRelation logic
valid = record
  { R = R
  ; R⟪and⟫ = R⟪and⟫
  ; R⟪or⟫ = R⟪or⟫
  ; R⟪not⟫ = R⟪not⟫
  ; R⟪<⟫ = R⟪<⟫
  ; R⟪≤⟫ = R⟪≤⟫
  }

------------------------------------------------------------------------------
-- Compilation

module _ (extFunc : ℚ → ℚ) where

  open import MiniVehicle.LossFunctions.GenericCompilation
    using (lossRestriction)
  open import MiniVehicle.Language.Syntax lossRestriction

  open import MiniVehicle.Language.Syntax.Restriction

  open import MiniVehicle.LossFunctions.GenericCorrectness extFunc logic valid as L
  open Equivalence
  
  prec : ℚ
  prec = + 1 / 10000000

  -- The calculation of the loss of any term
  loss : ε / ε ⊢ Bool (BoolRes U) → ℚ
  loss t with L.lossFunctionProp t
  ... | (t , f) = proj₁ f

  -- Correspondance with standard semantics
  true⇒loss≡0 : ∀ t → True (standardProp t) → loss t ≡ 0ℚ
  true⇒loss≡0 t tr with L.lossFunctionProp t | prop-correctness t
  ... | (t , f) | x rewrite True⇒true tr with x
  ...   | truthy y = refl
{-
  false⇒loss>0 : ∀ t → ¬ (True (standardProp t)) → loss t > 0ℚ
  false⇒loss>0 t ¬tr with L.lossFunctionProp t | prop-correctness t
  ... | (t , f) | x rewrite False⇒false ¬tr with x 
  ...   | falsey u = {!!}
-}
