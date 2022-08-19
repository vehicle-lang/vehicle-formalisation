{-# OPTIONS --postfix-projections --safe #-}

module StandardSemantics where

open import Level using (Lift; lift; lower)
open import Data.Bool using (true; false; _∧_; _∨_; not)
                   renaming (Bool to 𝔹; if_then_else_ to ifᵇ_then_else_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Rational using (ℚ; _≤ᵇ_) renaming (_+_ to _+ℚ_; _*_ to _*ℚ_)
open import Data.Unit using (⊤; tt)

open import MiniVehicle

⟦_⟧kind : Kind → Set₁
⟦ Nat ⟧kind  = Lift _ ℕ
⟦ Type ⟧kind = Set

⟦_⟧kctxt : KindContext → Set
⟦ ε ⟧kctxt      = ⊤
⟦ Δ ,-ℕ ⟧kctxt = ⟦ Δ ⟧kctxt × ℕ

⟦_⟧ty : ∀ {Δ κ} → Δ ⊢T κ → ⟦ Δ ⟧kctxt → ⟦ κ ⟧kind
⟦ Bool constraint ⟧ty δ = 𝔹
⟦ Num x ⟧ty           δ = ℚ
⟦ A ⇒ B ⟧ty          δ = ⟦ A ⟧ty δ → ⟦ B ⟧ty δ
⟦ Index n ⟧ty         δ = Fin (⟦ n ⟧ty δ .lower)
⟦ Array n A ⟧ty       δ = Fin (⟦ n ⟧ty δ .lower) → ⟦ A ⟧ty δ

⟦_⟧ctxt : ∀ {Δ} → Context Δ → ⟦ Δ ⟧kctxt → Set
⟦ ε ⟧ctxt      δ = ⊤
⟦ Γ ,- A ⟧ctxt δ = ⟦ Γ ⟧ctxt δ × ⟦ A ⟧ty δ

⟦_⟧var : ∀ {Δ Γ A} → Δ ⊢ Γ ∋ A → ∀ δ → ⟦ Γ ⟧ctxt δ → ⟦ A ⟧ty δ
⟦ zero ⟧var   δ (_ , a) = a
⟦ succ x ⟧var δ (γ , _) = ⟦ x ⟧var δ γ

module TermSem (f : ℚ → ℚ) where

  ⟦_⟧tm : ∀ {Δ Γ A} → Δ / Γ ⊢ A → ∀ δ → ⟦ Γ ⟧ctxt δ → ⟦ A ⟧ty δ
  ⟦ var x ⟧tm δ γ = ⟦ x ⟧var δ γ
  ⟦ ƛ t ⟧tm δ γ = λ a → ⟦ t ⟧tm δ (γ , a)
  ⟦ s ∙ t ⟧tm δ γ = ⟦ s ⟧tm δ γ (⟦ t ⟧tm δ γ)
  ⟦ func t ⟧tm δ γ = f (⟦ t ⟧tm δ γ)
  ⟦ const x ⟧tm δ γ = x
  ⟦ lift t ⟧tm δ γ = ⟦ t ⟧tm δ γ
  ⟦ s `+ t ⟧tm δ γ = (⟦ s ⟧tm δ γ) +ℚ (⟦ t ⟧tm δ γ)
  ⟦ s `* t ⟧tm δ γ = (⟦ s ⟧tm δ γ) *ℚ (⟦ t ⟧tm δ γ)

  ⟦ array n A t ⟧tm δ γ = λ idx → ⟦ t ⟧tm δ (γ , idx)
  ⟦ index n A s t ⟧tm δ γ = ⟦ s ⟧tm δ γ (⟦ t ⟧tm δ γ)

  ⟦ s `≤ t ⟧tm δ γ  = (⟦ s ⟧tm δ γ) ≤ᵇ (⟦ t ⟧tm δ γ)
  ⟦ if s then t else u ⟧tm δ γ = ifᵇ (⟦ s ⟧tm δ γ) then (⟦ t ⟧tm δ γ) else (⟦ u ⟧tm δ γ)
  ⟦ `¬ t ⟧tm δ γ = not (⟦ t ⟧tm δ γ)
  ⟦ s `∧ t ⟧tm δ γ = (⟦ s ⟧tm δ γ) ∧ (⟦ t ⟧tm δ γ)
  ⟦ s `∨ t ⟧tm δ γ = (⟦ s ⟧tm δ γ) ∨ (⟦ t ⟧tm δ γ)
