
module MiniVehicle.LossFunctions.Instantiation2 where

open import Data.Sum as Sum
open import Data.Product as Prod
open import Data.Rational
open import Data.Rational.Properties
open import Data.Bool hiding (_≤_; _<_; _<?_; _≤?_) renaming (Bool to 𝔹; T to True)
open import Data.Bool.Properties hiding (_<?_; _≤?_)
open import Data.Integer using (+_)
open import Data.Empty using (⊥-elim)
open import Algebra
open import Function
open import Function.Reasoning
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong; cong₂; refl; subst)
open import Relation.Unary using (Decidable)
open import Relation.Nullary.Negation

open import Util
open import MiniVehicle.Language.StandardSemantics
open import MiniVehicle.LossFunctions.GenericDifferentiableLogic

open DifferentiableLogic

------------------------------------------------------------------------------
-- Define the set of non-negative rationals and operations over them.

ℚ⁺ : Set
ℚ⁺ = Σ ℚ NonNegative

0ℚ⁺ : ℚ⁺
0ℚ⁺ = 0ℚ , _

max⁺ : Op₂ ℚ⁺
max⁺ (p , p⁺) (q , q⁺) = p ⊔ q , ⊔-pres-nonNegative p⁺ q⁺

min⁺ : Op₂ ℚ⁺
min⁺ (p , p⁺) (q , q⁺) = p ⊓ q , ⊓-pres-nonNegative p⁺ q⁺

min⁺-zeroʳ : RightZero _≡_ 0ℚ⁺ min⁺
min⁺-zeroʳ = {!!}

_+⁺_ : Op₂ ℚ⁺
(p , p⁺) +⁺ (q , q⁺) = p + q , +-pres-nonNegative {p} {q} p⁺ q⁺

_-_[_] : ∀ p q → p ≥ q → ℚ⁺
p - q [ p≥q ] = p - q , nonNegative (p≥q⇒p-q≥0 p≥q)

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
R⟪and⟫ (truthy p) (truthy q) = truthy (min⁺ p q)
R⟪and⟫ (truthy p) (falsey q) = subst (R false) (sym (cong₂ _,_ (min⁺-zeroʳ p) {!!})) (falsey q)
R⟪and⟫ (falsey p) (truthy q) = subst (R false) (sym (cong₂ _,_ {!min⁺-identityʳ q!} {!!})) (falsey p)
R⟪and⟫ (falsey p) (falsey q) = falsey (max⁺ p q)
{-
⟪or⟫-⇿ : R a p → R b q → R (a ∧ b) (p ⟦or⟧ q)
⟪or⟫-⇿ (pos p) (pos q) = mk⇔ (λ _ → truth (min⁺ p q)) (λ _ → inj₁ (truth p))
⟪or⟫-⇿ (pos p) (neg q) = mk⇔ (λ _ → truth q) (λ _ → inj₁ (truth p))
⟪or⟫-⇿ (neg p) (pos q) = mk⇔ (λ _ → truth p) (λ _ → inj₂ (truth q))
⟪or⟫-⇿ (neg p) (neg q) = mk⇔ (λ {(inj₁ ()); (inj₂ ())}) (λ())
-}

R⟪not⟫ : R a p → R (not a) (⟦not⟧ p)
R⟪not⟫ (truthy p) = falsey p
R⟪not⟫ (falsey p) = truthy p

R⟪≤⟫ : ∀ {p q} → R (p ≤ᵇ q) (p ⟦≤⟧ q)
R⟪≤⟫ {p} {q} with p ≤? q
... | yes p≤q rewrite True⇒true (≤⇒≤ᵇ p≤q) = truthy (q - p [ p≤q ])
... | no  p≰q = {!falsey ?!}

R⟪<⟫ : R (r <ᵇ s) (r ⟦<⟧ s)
R⟪<⟫ {r} {s} with r <? s
... | yes r<s = {!!}
... | no  r≮s = {!!}

valid : DifferentiableLogicRelation logic
valid = record
  { R = R
  ; R⟪and⟫ = R⟪and⟫
  ; R⟪or⟫ = {!!} --R⟪or⟫
  ; R⟪not⟫ = R⟪not⟫
  ; R⟪<⟫ = R⟪<⟫
  ; R⟪≤⟫ = R⟪≤⟫
  }
{-
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
  ... | pos _ = 0ℚ
  ... | neg (l , _) = l + prec

  -- Correspondance with standard semantics
  true⇒loss≡0 : ∀ t → True (standardProp t) → loss t ≡ 0ℚ
  true⇒loss≡0 t tr with L.lossFunctionProp t | f (prop-correctness t) tr
  ... | pos p | x = refl

  false⇒loss>0 : ∀ t → ¬ (True (standardProp t)) → loss t > 0ℚ
  false⇒loss>0 t ¬tr with L.lossFunctionProp t | g (prop-correctness t)
  ... | pos p | x = contradiction (x (truth p)) ¬tr
  ... | neg (l , l⁺) | x = positive⁻¹ (nonNegative+pos⇒pos {l} {prec} l⁺ _)
-}
