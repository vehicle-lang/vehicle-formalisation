module Util.PositiveRational where

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

------------------------------------------------------------------------------
-- Define the set of non-negative rationals and operations over them.

ℚ⁺ : Set
ℚ⁺ = Σ ℚ NonNegative

0ℚ⁺ : ℚ⁺
0ℚ⁺ = 0ℚ , _

abstract

  max⁺ : Op₂ ℚ⁺
  max⁺ (p , p⁺) (q , q⁺) = p ⊔ q , ⊔-pres-nonNegative p⁺ q⁺

  min⁺ : Op₂ ℚ⁺
  min⁺ (p , p⁺) (q , q⁺) = p ⊓ q , ⊓-pres-nonNegative p⁺ q⁺

  _+⁺_ : Op₂ ℚ⁺
  (p , p⁺) +⁺ (q , q⁺) = p + q , +-pres-nonNegative {p} {q} p⁺ q⁺

  _-_[_] : ∀ p q → p ≥ q → ℚ⁺
  p - q [ p≥q ] = p - q , nonNegative (p≥q⇒p-q≥0 p≥q)


------------------------------------------------------------------------------
-- Properties

  postulate min⁺-zeroʳ : RightZero _≡_ 0ℚ⁺ min⁺
  -- min⁺-zeroʳ = {!!}

  postulate min⁺-zeroˡ : LeftZero _≡_ 0ℚ⁺ min⁺
  -- min⁺-zeroˡ = {!!}

  postulate min⁺-identityʳ : RightIdentity _≡_ 0ℚ⁺ min⁺
  -- min⁺-identityʳ = {!!}

  postulate min⁺-identityˡ : LeftIdentity _≡_ 0ℚ⁺ min⁺
  -- min⁺-identityˡ = {!!}

  postulate max⁺-zeroʳ : RightZero _≡_ 0ℚ⁺ max⁺
  -- max⁺-zeroʳ = {!!}

  postulate max⁺-zeroˡ : LeftZero _≡_ 0ℚ⁺ max⁺
  -- max⁺-zeroˡ = {!!}

  postulate max⁺-identityˡ : LeftIdentity _≡_ 0ℚ⁺ max⁺
  -- max⁺-identityˡ = {!!}

  postulate max⁺-identityʳ : RightIdentity _≡_ 0ℚ⁺ max⁺
  -- max⁺-identityʳ = {!!}
