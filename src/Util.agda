{-# OPTIONS --postfix-projections --safe #-}

module Util where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

is-true-or-false : ∀ b → (b ≡ true) ⊎ (b ≡ false)
is-true-or-false false = inj₂ refl
is-true-or-false true = inj₁ refl

cong₃ : ∀ {a b c d} {A : Set a}{B : Set b}{C : Set c}{D : Set d} (f : A → B → C → D) {x y u v t w} → x ≡ y → u ≡ v → t ≡ w → f x u t ≡ f y v w
cong₃ f refl refl refl = refl
