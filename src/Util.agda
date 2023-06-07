{-# OPTIONS --safe #-}

module Util where

open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open import Data.Product as Prod
open import Function
open import Level using (Level)
open import Data.Rational
open import Data.Rational.Properties
open import Function.Properties.Equivalence

open Equivalence
 
private
  variable
    a b c d : Level
    A B C D : Set a
    
------------------------------------------------------------------------------
-- Basics

is-true-or-false : ∀ b → (b ≡ true) ⊎ (b ≡ false)
is-true-or-false false = inj₂ refl
is-true-or-false true = inj₁ refl

cong₃ : ∀ (f : A → B → C → D) {x y u v t w} → x ≡ y → u ≡ v → t ≡ w → f x u t ≡ f y v w
cong₃ f refl refl refl = refl

_Pres₁_⟶_ : ∀ (f : A → B) → (A → Set a) → (B → Set c) → Set _
f Pres₁ P ⟶ Q = ∀ {x} → P x → Q (f x)

_Pres₂_⟶_ : ∀ (f : A → B) → (A → A → Set a) → (B → B → Set c) → Set _
f Pres₂ P ⟶ Q = ∀ {x y} → P x y → Q (f x) (f y)

_Pres₃_⟶_ : ∀ (f : A → B) → (A → A → A → Set a) → (B → B → B → Set c) → Set _
f Pres₃ P ⟶ Q = ∀ {x y z} → P x y z → Q (f x) (f y) (f z)

------------------------------------------------------------------------------
-- Equivalence reasoning

module ⇔-Reasoning {ℓ} where
  import Relation.Binary.Reasoning.Setoid as SetoidReasoning

  module Reasoning = SetoidReasoning (record
    { Carrier       = Set ℓ
    ; _≈_           = _⇔_
    ; isEquivalence = ⇔-isEquivalence
    })

  open Reasoning public hiding (step-≈; step-≈˘)

  infixr 1 step-⇔ step-⇔˘

  step-⇔  = Reasoning.step-≈
  step-⇔˘ = Reasoning.step-≈˘

  syntax step-⇔ x y∼z x⇔y = x ⇔⟨  x⇔y ⟩ y∼z
  syntax step-⇔˘ x y∼z y⇔x = x ⇔˘⟨ y⇔x ⟩ y∼z
  
-- Will be in stdlib v2.0
_×-⇔_ : A ⇔ B → C ⇔ D → (A × C) ⇔ (B × D)
A⇔B ×-⇔ C⇔D = mk⇔ (Prod.map (f A⇔B) (f C⇔D)) (Prod.map (g A⇔B) (g C⇔D))

-- Will be in stdlib v2.0
_⊎-⇔_ : A ⇔ B → C ⇔ D → (A ⊎ C) ⇔ (B ⊎ D)
A⇔B ⊎-⇔ C⇔D = mk⇔ (Sum.map (f A⇔B) (f C⇔D)) (Sum.map (g A⇔B) (g C⇔D))

-- Will be in stdlib v2.0
Σ-⇔ : ∀ {A : Set} {B₁ : A → Set} {B₂ : A → Set}  →
      (∀ {x} → B₁ x ⇔ B₂ x) →
      Σ A B₁ ⇔ Σ A B₂
Σ-⇔ B₁⇔B₂ = mk⇔ (Prod.map₂ (f B₁⇔B₂)) (Prod.map₂ (g B₁⇔B₂))
  
------------------------------------------------------------------------------
-- Rational proofs

-- Should be in v2.0
p≤q⇒p-q≤0 : ∀ {p q} → p ≤ q → p - q ≤ 0ℚ
p≤q⇒p-q≤0 {p} {q} p≤q = begin
  p - q ≤⟨ +-monoˡ-≤ (- q) p≤q ⟩
  q - q ≡⟨ +-inverseʳ q ⟩
  0ℚ    ∎ where open ≤-Reasoning

-- Should be in v2.0
p-q≤0⇒p≤q : ∀ {p q} → p - q ≤ 0ℚ → p ≤ q
p-q≤0⇒p≤q {p} {q} p-q≤0 = begin
  p             ≡˘⟨ +-identityʳ p ⟩
  p + 0ℚ       ≡⟨ P.cong (p +_) (P.sym (+-inverseˡ q)) ⟩
  p + (- q + q) ≡˘⟨ +-assoc p (- q) q ⟩
  (p - q) + q   ≤⟨ +-monoˡ-≤ q p-q≤0 ⟩
  0ℚ + q       ≡⟨ +-identityˡ q ⟩
  q             ∎ where open ≤-Reasoning
