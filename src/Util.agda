{-# OPTIONS --safe #-}

module Util where

open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not) renaming (T to True)
open import Data.Bool.Properties using ()
open import Data.Product as Prod
open import Data.Rational
open import Data.Rational.Properties
open import Data.Empty
open import Data.Unit using (tt)
import Data.Integer.Properties as ℤ
open import Function
open import Function.Properties.Equivalence using (⇔-isEquivalence)
open import Level using (Level)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation
open import Relation.Binary using (_⇒_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)

open Equivalence

private
  variable
    a b c d : Level
    A B C D : Set a
    p q : ℚ

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
-- Boolean

True⇒true : ∀ {a} → True a → a ≡ true
True⇒true {true} tt = refl

False⇒false : ∀ {a} → ¬ (True a) → a ≡ false
False⇒false {false} t = refl
False⇒false {true} t = ⊥-elim (t tt)

True-∧⁺ : ∀ {a b} → True a × True b → True (a ∧ b)
True-∧⁺ {true} {true} _ = _

True-∧⁻ : ∀ {a b} → True (a ∧ b) → True a × True b
True-∧⁻ {true} {true} _ = _ , _

True-∧-⇔ : ∀ {a b} → (True a × True b) ⇔ True (a ∧ b)
True-∧-⇔ = mk⇔ True-∧⁺ True-∧⁻

True-∨⁺ : ∀ {a b} → True a ⊎ True b → True (a ∨ b)
True-∨⁺ {true} {_} (inj₁ _) = _
True-∨⁺ {true} {true} (inj₂ _) = tt
True-∨⁺ {false} {true} (inj₂ _) = tt

True-∨⁻ : ∀ {a b} → True (a ∨ b) → True a ⊎ True b
True-∨⁻ {_} {true} _ = inj₂ _
True-∨⁻ {true} {_} _ = inj₁ _

True-∨-⇔ : ∀ {a b} → (True a ⊎ True b) ⇔ True (a ∨ b)
True-∨-⇔ = mk⇔ True-∨⁺ True-∨⁻

True-not⁻ : ∀ {a} → True (not a) → ¬ True a
True-not⁻ {false} _ = id

True-not⁺ : ∀ {a} → ¬ True a → True (not a)
True-not⁺ {false} _ = _
True-not⁺ {true}  v = v _

True-not-⇔ : ∀ {a} → (¬ True a) ⇔ True (not a)
True-not-⇔ = mk⇔ True-not⁺ True-not⁻

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

  infixr 2 step-⇔ step-⇔˘

  step-⇔  = Reasoning.step-≈
  step-⇔˘ = Reasoning.step-≈˘

  syntax step-⇔ x y∼z x⇔y = x ⇔⟨  x⇔y ⟩ y∼z
  syntax step-⇔˘ x y∼z y⇔x = x ⇔⟨ y⇔x ⟨ y∼z
  
-- Will be in stdlib v2.0
_×-⇔_ : A ⇔ B → C ⇔ D → (A × C) ⇔ (B × D)
A⇔B ×-⇔ C⇔D = mk⇔ (Prod.map (to A⇔B) (to C⇔D)) (Prod.map (from A⇔B) (from C⇔D))

-- Will be in stdlib v2.0
_⊎-⇔_ : A ⇔ B → C ⇔ D → (A ⊎ C) ⇔ (B ⊎ D)
A⇔B ⊎-⇔ C⇔D = mk⇔ (Sum.map (to A⇔B) (to C⇔D)) (Sum.map (from A⇔B) (from C⇔D))

-- Will be in stdlib v2.0
Σ-⇔ : ∀ {A : Set} {B₁ : A → Set} {B₂ : A → Set}  →
      (∀ {x} → B₁ x ⇔ B₂ x) →
      Σ A B₁ ⇔ Σ A B₂
Σ-⇔ B₁⇔B₂ = mk⇔ (Prod.map₂ (to B₁⇔B₂)) (Prod.map₂ (from B₁⇔B₂))

¬-⇔ : A ⇔ B → (¬ A) ⇔ (¬ B)
¬-⇔ A⇔B = mk⇔ (_∘ from A⇔B) (_∘ to A⇔B)

¬?-→ : Dec A → Dec B → (¬ A → ¬ B) → B → A
¬?-→ (yes A) _       ¬A⇔¬B = const A
¬?-→ (no ¬A) (yes B) ¬A⇔¬B = contradiction B (¬A⇔¬B ¬A)
¬?-→ (no ¬A) (no ¬B) ¬A⇔¬B = ⊥-elim ∘ ¬B

¬?-⇔ : Dec A → Dec B → (¬ A) ⇔ (¬ B) → A ⇔ B
¬?-⇔ (yes A) (yes B) ¬A⇔¬B = mk⇔ (const B) (const A)
¬?-⇔ (yes A) (no ¬B) ¬A⇔¬B = contradiction A (from ¬A⇔¬B ¬B)
¬?-⇔ (no ¬A) (yes B) ¬A⇔¬B = contradiction B (to ¬A⇔¬B ¬A)
¬?-⇔ (no ¬A) (no ¬B) ¬A⇔¬B = mk⇔ (⊥-elim ∘ ¬A )(⊥-elim ∘ ¬B)

------------------------------------------------------------------------------
-- Additional ℚ utilities

infix 4 _<ᵇ_
_<ᵇ_ : ℚ → ℚ → Bool
p <ᵇ q = not (q ≤ᵇ p)

-- Should be in v2.0
p≥q⇒p-q≥0 : p ≥ q → p - q ≥ 0ℚ
p≥q⇒p-q≥0 {p} {q} p≥q = begin
  0ℚ   ≡˘⟨ +-inverseʳ p ⟩
  p - p ≤⟨ +-monoʳ-≤ p (neg-antimono-≤ p≥q) ⟩
  p - q ∎ where open ≤-Reasoning


-- Should be in v2.0
p≤q⇒p-q≤0 : p ≤ q → p - q ≤ 0ℚ
p≤q⇒p-q≤0 {p} {q} p≤q = begin
  p - q ≤⟨ +-monoˡ-≤ (- q) p≤q ⟩
  q - q ≡⟨ +-inverseʳ q ⟩
  0ℚ    ∎ where open ≤-Reasoning

-- Should be in v2.0
p-q≤0⇒p≤q : p - q ≤ 0ℚ → p ≤ q
p-q≤0⇒p≤q {p} {q} p-q≤0 = begin
  p             ≡˘⟨ +-identityʳ p ⟩
  p + 0ℚ       ≡⟨ P.cong (p +_) (P.sym (+-inverseˡ q)) ⟩
  p + (- q + q) ≡˘⟨ +-assoc p (- q) q ⟩
  (p - q) + q   ≤⟨ +-monoˡ-≤ q p-q≤0 ⟩
  0ℚ + q       ≡⟨ +-identityˡ q ⟩
  q             ∎ where open ≤-Reasoning

p≤q⇔p-q≤0 : p ≤ q ⇔ p - q ≤ 0ℚ
p≤q⇔p-q≤0 = mk⇔ p≤q⇒p-q≤0 p-q≤0⇒p≤q

≰⇒≥ : p ≰ q → p ≥ q

≰⇒≥ = <⇒≤ ∘ ≰⇒>

<⇒≱ : _<_ ⇒ _≱_
<⇒≱ p<q = ℤ.<⇒≱ (drop-*<* p<q) ∘ drop-*≤*

≤ᵇ⇔≤ : True (p ≤ᵇ q) ⇔ p ≤ q
≤ᵇ⇔≤ = mk⇔ ≤ᵇ⇒≤ ≤⇒≤ᵇ

<⇒<ᵇ : p < q → True (p <ᵇ q)
<⇒<ᵇ p<q = True-not⁺ (<⇒≱ p<q ∘ ≤ᵇ⇒≤)

<ᵇ⇒< : True (p <ᵇ q) → p < q
<ᵇ⇒< p<ᵇq = ≰⇒> (True-not⁻ p<ᵇq ∘ ≤⇒≤ᵇ)

<ᵇ⇔< : True (p <ᵇ q) ⇔ p < q
<ᵇ⇔< = mk⇔ <ᵇ⇒< <⇒<ᵇ

⊔-pres-nonNegative : ∀ (p q : ℚ) {{_ : NonNegative p}} {{_ : NonNegative q}} → NonNegative (p ⊔ q)
⊔-pres-nonNegative p@record{} q@record{} {{p⁺}} {{q⁺}} with p ≤ᵇ q
... | true  = q⁺
... | false = p⁺

⊓-pres-nonNegative : ∀ (p q : ℚ) {{_ : NonNegative p}} {{_ : NonNegative q}} → NonNegative (p ⊓ q)
⊓-pres-nonNegative p@record{} q@record{} {{p⁺}} {{q⁺}} with p ≤ᵇ q
... | true  = p⁺
... | false = q⁺

+-pres-nonNegative : (p q : ℚ) {{_ : NonNegative p}} {{_ : NonNegative q}} → NonNegative (p + q)
+-pres-nonNegative p q = nonNegative (+-mono-≤ (nonNegative⁻¹ p) (nonNegative⁻¹ q))

nonNegative+pos⇒pos : (p q : ℚ) {{_ : NonNegative p}} {{_ : Positive q}} → Positive (p + q)
nonNegative+pos⇒pos p q = positive (+-mono-≤-< (nonNegative⁻¹ p) (positive⁻¹ q))
