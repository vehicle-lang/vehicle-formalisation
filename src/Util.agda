{-# OPTIONS --safe #-}

module Util where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Level using (Level)

private
  variable
    a b c d : Level
    A B C D : Set a
    
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
