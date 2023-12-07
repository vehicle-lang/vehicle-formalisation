
module MiniVehicle.LossFunctions.Instantiation1 where

open import Data.Sum as Sum
open import Data.Product as Prod
open import Data.Rational hiding (pos; neg)
open import Data.Rational.Properties
open import Data.Bool hiding (_≤_; _<_; _<?_; _≤?_) renaming (Bool to 𝔹; T to True)
open import Data.Bool.Properties hiding (_<?_; _≤?_)
open import Data.Integer using (+_)
open import Data.Empty using (⊥-elim)
open import Algebra
open import Function
open import Function.Reasoning
open import Relation.Nullary hiding (True)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl)
open import Relation.Unary using (Decidable)
open import Relation.Nullary.Negation

open import Util
open import Util.PositiveRational
open import MiniVehicle.Language.StandardSemantics
open import MiniVehicle.LossFunctions.GenericDifferentiableLogic

open DifferentiableLogic

------------------------------------------------------------------------------
-- Define the signed non-negative rationals.

data ±ℚ : Set where
  pos : (p : ℚ⁺) → ±ℚ
  neg : (p : ℚ⁺) → ±ℚ

_⟦and⟧_ : ±ℚ → ±ℚ → ±ℚ
pos x ⟦and⟧ pos y = pos (max⁺ x y)
pos x ⟦and⟧ neg y = neg y
neg x ⟦and⟧ pos y = neg x
neg x ⟦and⟧ neg y = neg (min⁺ x y)

_⟦or⟧_ : ±ℚ → ±ℚ → ±ℚ
pos x ⟦or⟧ pos y = pos (min⁺ x y)
pos x ⟦or⟧ neg y = pos y
neg x ⟦or⟧ pos y = pos x
neg x ⟦or⟧ neg y = neg (max⁺ x y)

⟦not⟧_ : ±ℚ → ±ℚ
⟦not⟧ pos x = neg x
⟦not⟧ neg x = pos x

_⟦≤⟧_ : ℚ → ℚ → ±ℚ
x ⟦≤⟧ y with x ≤? y
... | yes x≤y = pos (y - x , nonNegative (p≥q⇒p-q≥0 x≤y))
... | no  x≰y = neg (x - y , nonNegative (p≥q⇒p-q≥0 (≰⇒≥ x≰y)))

_⟦<⟧_ : ℚ → ℚ → ±ℚ
x ⟦<⟧ y with x <? y
... | yes x<y = pos (y - x , nonNegative (p≥q⇒p-q≥0 (<⇒≤ x<y)))
... | no  x≮y = neg (x - y , nonNegative (p≥q⇒p-q≥0 (≮⇒≥ x≮y)))

logic : DifferentiableLogic
logic .⟪Bool⟫ = ±ℚ
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
    p q r : ±ℚ

data Truish : ±ℚ → Set where
  truth : ∀ q → Truish (pos q)

Truish? : Decidable Truish
Truish? (pos p) = yes (truth p)
Truish? (neg p) = no λ()

⟪and⟫-⇿ : ∀ p q → (Truish p × Truish q) ⇔ (Truish (p ⟦and⟧ q))
⟪and⟫-⇿ (pos p) (pos q) = mk⇔ (λ _ → truth (max⁺ p q)) (λ _ → truth p , truth q)
⟪and⟫-⇿ (pos p) (neg q) = mk⇔ (λ()) (λ())
⟪and⟫-⇿ (neg p) (pos q) = mk⇔ (λ()) (λ())
⟪and⟫-⇿ (neg p) (neg q) = mk⇔ (λ()) (λ())

⟪or⟫-⇿ : ∀ p q → (Truish p ⊎ Truish q) ⇔ (Truish (p ⟦or⟧ q))
⟪or⟫-⇿ (pos p) (pos q) = mk⇔ (λ _ → truth (min⁺ p q)) (λ _ → inj₁ (truth p))
⟪or⟫-⇿ (pos p) (neg q) = mk⇔ (λ _ → truth q) (λ _ → inj₁ (truth p))
⟪or⟫-⇿ (neg p) (pos q) = mk⇔ (λ _ → truth p) (λ _ → inj₂ (truth q))
⟪or⟫-⇿ (neg p) (neg q) = mk⇔ (λ {(inj₁ ()); (inj₂ ())}) (λ())

⟪not⟫-⇿ : ∀ p → Truish p ⇔ (¬ (Truish (⟦not⟧ p)))
⟪not⟫-⇿ (pos p)   = mk⇔ (λ _ ()) (λ _ → truth p)
⟪not⟫-⇿ (neg p) = mk⇔ (λ()) (λ f → ⊥-elim (f (truth p)))

⟪<⟫-⇿ : ∀ p q → True (p <ᵇ q) ⇔ Truish (p ⟦<⟧ q)
⟪<⟫-⇿ p q with p <? q
... | yes p<q = mk⇔ (λ p<ᵇq → truth _) (λ _ → <⇒<ᵇ p<q)
... | no  p≮q = mk⇔ (λ p<ᵇq → ⊥-elim (p≮q (<ᵇ⇒< p<ᵇq))) λ()

⟪≤⟫-⇿ : ∀ p q → True (p ≤ᵇ q) ⇔ Truish (p ⟦≤⟧ q)
⟪≤⟫-⇿ p q with p ≤? q
... | yes p≤q = mk⇔ (λ p≤ᵇq → truth _) (λ _ → ≤⇒≤ᵇ p≤q)
... | no  p≰q = mk⇔ (λ p≤ᵇq → ⊥-elim (p≰q (≤ᵇ⇒≤ p≤ᵇq))) λ()

valid : DifferentiableLogicRelation logic
valid = predicateToRelation logic $ record
  { Truish = Truish
  ; Truish? = Truish?
  ; ⟪and⟫-⇿ = ⟪and⟫-⇿
  ; ⟪or⟫-⇿ = ⟪or⟫-⇿
  ; ⟪not⟫-⇿ = ⟪not⟫-⇿
  ; ⟪<⟫-⇿ = ⟪<⟫-⇿
  ; ⟪≤⟫-⇿ = ⟪≤⟫-⇿
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
  ... | pos _ = 0ℚ
  ... | neg (l , _) = l + prec

  -- Correspondance with standard semantics
  true⇒loss≡0 : ∀ t → True (standardProp t) → loss t ≡ 0ℚ
  true⇒loss≡0 t tr with L.lossFunctionProp t | to (prop-correctness t) tr
  ... | pos p | x = refl

  false⇒loss>0 : ∀ t → ¬ (True (standardProp t)) → loss t > 0ℚ
  false⇒loss>0 t ¬tr with L.lossFunctionProp t | from (prop-correctness t)
  ... | pos p | x = contradiction (x (truth p)) ¬tr
  ... | neg (l , l⁺) | x = positive⁻¹ (l + prec) {{nonNegative+pos⇒pos l prec {{l⁺}}}}
