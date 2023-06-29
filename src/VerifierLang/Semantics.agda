{-# OPTIONS --safe #-}

open import Data.Bool
       using (Bool; true; false; _∧_; _∨_; if_then_else_; not)
       renaming (T to True)
open import Data.Bool.Properties using (not-involutive; ∨-∧-booleanAlgebra)
open import Algebra.Properties.BooleanAlgebra ∨-∧-booleanAlgebra using (deMorgan₁; deMorgan₂)
open import Data.Product using (Σ-syntax; _×_)
open import Data.Sum using (_⊎_)
open import Data.Rational as ℚ using (ℚ; 1ℚ; _*_; _+_; _≤ᵇ_; _≟_)
open import Data.Rational.Properties using (*-assoc; *-distribˡ-+)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong₂)
open import Util using (_<ᵇ_)

open import VerifierLang.Syntax

module VerifierLang.Semantics (extFunc : ℚ → ℚ) where

Env : LinVarCtxt → Set
Env Δ = Var Δ → ℚ

empty-env : Env ε
empty-env ()

extend-env : ∀ {Δ} → Env Δ → ℚ → Env (Δ ,∙)
extend-env η q zero     = q
extend-env η q (succ x) = η x

eval-LinExp : ∀ {Δ} → LinExp Δ → Env Δ → ℚ
eval-LinExp (const q)   η = q
eval-LinExp (var q x)   η = q * η x
eval-LinExp (e₁ `+` e₂) η = eval-LinExp e₁ η + eval-LinExp e₂ η

eval-⊛ : ∀ {Δ} q (e : LinExp Δ) η → q * eval-LinExp e η ≡ eval-LinExp (q ⊛ e) η
eval-⊛ q (const x) η = refl
eval-⊛ q (var r x) η = sym (*-assoc q r (η x))
eval-⊛ q (e₁ `+` e₂) η rewrite sym (eval-⊛ q e₁ η) rewrite sym (eval-⊛ q e₂ η) =
  *-distribˡ-+ q (eval-LinExp e₁ η) (eval-LinExp e₂ η)

eval-Constraint : ∀ {Δ} → Constraint Δ → Env Δ → Bool
eval-Constraint (e₁ `≤` e₂)  η = eval-LinExp e₁ η ≤ᵇ eval-LinExp e₂ η
eval-Constraint (e₁ `<` e₂)  η = eval-LinExp e₁ η <ᵇ eval-LinExp e₂ η
eval-Constraint (e₁ `=` e₂)  η = (eval-LinExp e₁ η ≟ eval-LinExp e₂ η) .does
eval-Constraint (e₁ `≠` e₂)  η = not ((eval-LinExp e₁ η ≟ eval-LinExp e₂ η) .does)
eval-Constraint (p and q)    η = eval-Constraint p η ∧ eval-Constraint q η
eval-Constraint (p or q)     η = eval-Constraint p η ∨ eval-Constraint q η
eval-Constraint (x₁ `=`f x₂) η = (η x₁ ≟ extFunc (η x₂)) .does
eval-Constraint (x₁ `≠`f x₂) η = not ((η x₁ ≟ extFunc (η x₂)) .does)

eval-negate : ∀ {Δ} (p : Constraint Δ) η →
              not (eval-Constraint p η) ≡ eval-Constraint (negate p) η
eval-negate (x `≤` x₁) η = refl
eval-negate (x `<` x₁) η = not-involutive _
eval-negate (x `=` x₁) η = refl
eval-negate (x `≠` x₁) η = not-involutive _
eval-negate (p and q)  η rewrite sym (eval-negate p η)
                         rewrite sym (eval-negate q η) =
                            deMorgan₁ (eval-Constraint p η) (eval-Constraint q η)
eval-negate (p or q)   η rewrite sym (eval-negate p η)
                         rewrite sym (eval-negate q η) =
                            deMorgan₂ (eval-Constraint p η) (eval-Constraint q η)
eval-negate (x₁ `=`f x₂) η = refl
eval-negate (x₁ `≠`f x₂) η = not-involutive _


eval-ExFormula : ∀ {Δ} → ExFormula Δ → Env Δ → Set
eval-ExFormula (constraint ϕ) η = True (eval-Constraint ϕ η)
eval-ExFormula (ex ϕ) η = Σ[ q ∈ ℚ ] eval-ExFormula ϕ (extend-env η q)
eval-ExFormula (ϕ and ψ) η = eval-ExFormula ϕ η × eval-ExFormula ψ η
eval-ExFormula (ϕ or ψ) η = eval-ExFormula ϕ η ⊎ eval-ExFormula ψ η

eval-PrenexFormula : ∀ {Δ} → PrenexFormula Δ → Env Δ → Set
eval-PrenexFormula (constraint ϕ) η = True (eval-Constraint ϕ η)
eval-PrenexFormula (ex ϕ) η = Σ[ q ∈ ℚ ] (eval-PrenexFormula ϕ (extend-env η q))
