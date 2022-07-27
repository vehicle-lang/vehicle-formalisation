{-# OPTIONS --postfix-projections --safe #-}

module StandardSemantics where

open import Data.Bool using (true; false; _∧_; _∨_; not)
                   renaming (Bool to 𝔹; if_then_else_ to ifᵇ_then_else_)
open import Data.Product using (_×_; _,_)
open import Data.Rational using (ℚ; _≤ᵇ_) renaming (_+_ to _+ℚ_; _*_ to _*ℚ_)
open import Data.Unit using (⊤; tt)

open import MiniVehicle

⟦_⟧ty : Type → Set
⟦ Bool constraint ⟧ty = 𝔹
⟦ Num x ⟧ty           = ℚ
⟦ A ⇒ B ⟧ty          = ⟦ A ⟧ty → ⟦ B ⟧ty

⟦_⟧ctxt : Context → Set
⟦ ε ⟧ctxt      = ⊤
⟦ Γ ,- A ⟧ctxt = ⟦ Γ ⟧ctxt × ⟦ A ⟧ty

⟦_⟧var : ∀ {Γ A} → Γ ∋ A → ⟦ Γ ⟧ctxt → ⟦ A ⟧ty
⟦ zero ⟧var   (_ , a) = a
⟦ succ x ⟧var (γ , _) = ⟦ x ⟧var γ

module TermSem (f : ℚ → ℚ) where

  ⟦_⟧tm : ∀ {Γ A} → Γ ⊢ A → ⟦ Γ ⟧ctxt → ⟦ A ⟧ty
  ⟦ var x ⟧tm γ = ⟦ x ⟧var γ
  ⟦ ƛ t ⟧tm γ = λ a → ⟦ t ⟧tm (γ , a)
  ⟦ s ∙ t ⟧tm γ = ⟦ s ⟧tm γ (⟦ t ⟧tm γ)
  ⟦ func t ⟧tm γ = f (⟦ t ⟧tm γ)
  ⟦ const x ⟧tm γ = x
  ⟦ lift t ⟧tm γ = ⟦ t ⟧tm γ
  ⟦ s `+ t ⟧tm γ = (⟦ s ⟧tm γ) +ℚ (⟦ t ⟧tm γ)
  ⟦ s `* t ⟧tm γ = (⟦ s ⟧tm γ) *ℚ (⟦ t ⟧tm γ)
  ⟦ s `≤ t ⟧tm γ  = (⟦ s ⟧tm γ) ≤ᵇ (⟦ t ⟧tm γ)
  ⟦ if s then t else u ⟧tm γ = ifᵇ (⟦ s ⟧tm γ) then (⟦ t ⟧tm γ) else (⟦ u ⟧tm γ)
  ⟦ `¬ t ⟧tm γ = not (⟦ t ⟧tm γ)
  ⟦ s `∧ t ⟧tm γ = (⟦ s ⟧tm γ) ∧ (⟦ t ⟧tm γ)
  ⟦ s `∨ t ⟧tm γ = (⟦ s ⟧tm γ) ∨ (⟦ t ⟧tm γ)
