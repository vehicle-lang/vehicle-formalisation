{-# OPTIONS --postfix-projections #-}

module Expansion where

open import Data.Bool renaming (T to True)
open import Data.Product using (Σ-syntax; _×_)
open import Data.Sum using (_⊎_)
open import Data.Rational using (ℚ; 1ℚ)

open import NormalisedExpr
open import NormalisationCorrect
open import Isomorphism

data FlatQuery : LinVarCtxt → Set where
  constraint : ∀ {Δ} → ConstraintExp Δ → FlatQuery Δ
  ex         : ∀ {Δ} → FlatQuery (Δ ,∙) → FlatQuery Δ

rename-FlatQuery : ∀ {Δ Δ'} → (ρ : Δ' ⇒ᵣ Δ) → FlatQuery Δ → FlatQuery Δ'
rename-FlatQuery ρ (constraint x) = constraint (rename-ConstraintExp ρ x)
rename-FlatQuery ρ (ex ϕ) = ex (rename-FlatQuery (under ρ) ϕ)

conj-constraint : ∀ {Δ} → ConstraintExp Δ → FlatQuery Δ → FlatQuery Δ
conj-constraint ϕ (constraint ψ) = constraint (ϕ and ψ)
conj-constraint ϕ (ex ψ) = ex (conj-constraint (rename-ConstraintExp succ ϕ) ψ)

conj : ∀ {Δ} → FlatQuery Δ → FlatQuery Δ → FlatQuery Δ
conj (constraint ϕ) ψ = conj-constraint ϕ ψ
conj (ex ϕ)         ψ = ex (conj ϕ (rename-FlatQuery succ ψ))

disj-constraint : ∀ {Δ} → ConstraintExp Δ → FlatQuery Δ → FlatQuery Δ
disj-constraint ϕ (constraint ψ) = constraint (ϕ or ψ)
disj-constraint ϕ (ex ψ) = ex (disj-constraint (rename-ConstraintExp succ ϕ) ψ)

disj : ∀ {Δ} → FlatQuery Δ → FlatQuery Δ → FlatQuery Δ
disj (constraint ϕ) ψ = disj-constraint ϕ ψ
disj (ex ϕ) ψ = ex (disj ϕ (rename-FlatQuery succ ψ))



module _ (extFunc : ℚ → ℚ) where

  eval-FlatQuery : ∀ {Δ} → FlatQuery Δ → Env Δ → Set
  eval-FlatQuery (constraint ϕ) η = True (eval-ConstraintExp extFunc ϕ η)
  eval-FlatQuery (ex ϕ) η = Σ[ q ∈ ℚ ] (eval-FlatQuery ϕ (extend-env η q))

  ext-FlatQuery : ∀ {w₁ w₂} (ρ : w₂ ⇒w w₁) ϕ →
                  eval-FlatQuery ϕ (w₁ .env) ⇔
                     eval-FlatQuery (rename-FlatQuery (ρ .ren) ϕ) (w₂ .env)
  ext-FlatQuery ρ (constraint ϕ) = cong-True (ext-evalConstraint extFunc ϕ ρ)
  ext-FlatQuery ρ (ex ϕ) = cong-∃ λ q → ext-FlatQuery (under-w ρ) ϕ

  equi-conj-constraint : ∀ {Δ} (ϕ : ConstraintExp Δ) ψ η →
                         (True (eval-ConstraintExp extFunc ϕ η) × eval-FlatQuery ψ η)
                            ⇔ eval-FlatQuery (conj-constraint ϕ ψ) η
  equi-conj-constraint ϕ (constraint x) η = True-∧
  equi-conj-constraint ϕ (ex ψ) η =
    ⇔-trans
      and-comm-left
      (⇔-trans
       (cong-∃ λ q → ×-cong (cong-True (ext-evalConstraint extFunc ϕ wk-w)) ⇔-refl)
       (cong-∃ λ q →
          equi-conj-constraint (rename-ConstraintExp succ ϕ) ψ (extend-env η q)))

  equi-conj : ∀ {Δ} (ϕ : FlatQuery Δ) ψ η →
              (eval-FlatQuery ϕ η × eval-FlatQuery ψ η) ⇔ eval-FlatQuery (conj ϕ ψ) η
  equi-conj (constraint ϕ) ψ η = equi-conj-constraint ϕ ψ η
  equi-conj (ex ϕ) ψ η =
    ⇔-trans
     and-comm-right
     (cong-∃ λ q →
      ⇔-trans
       (×-cong ⇔-refl (ext-FlatQuery wk-w ψ))
       (equi-conj ϕ (rename-FlatQuery succ ψ) (extend-env η q)))

  equi-disj-constraint : ∀ {Δ} (ϕ : ConstraintExp Δ) ψ η →
                         (True (eval-ConstraintExp extFunc ϕ η) ⊎ eval-FlatQuery ψ η)
                            ⇔ eval-FlatQuery (disj-constraint ϕ ψ) η
  equi-disj-constraint ϕ (constraint x) η = True-∨
  equi-disj-constraint ϕ (ex ψ) η =
    ⇔-trans
     (or-comm-right 1ℚ)
     (cong-∃
      λ q → ⇔-trans
             (⊎-cong (cong-True (ext-evalConstraint extFunc ϕ wk-w)) ⇔-refl)
             (equi-disj-constraint (rename-ConstraintExp succ ϕ) ψ (extend-env η q)))

  equi-disj : ∀ {Δ} (ϕ : FlatQuery Δ) ψ η →
              (eval-FlatQuery ϕ η ⊎ eval-FlatQuery ψ η) ⇔ eval-FlatQuery (disj ϕ ψ) η
  equi-disj (constraint ϕ) ψ η = equi-disj-constraint ϕ ψ η
  equi-disj (ex ϕ) ψ η =
    ⇔-trans (or-comm-left 1ℚ)
     (cong-∃ λ q →
      ⇔-trans
       (⊎-cong ⇔-refl (ext-FlatQuery wk-w ψ))
       (equi-disj ϕ (rename-FlatQuery succ ψ) (extend-env η q)))

  flatten : ∀ {Δ} → Query Δ → FlatQuery Δ
  flatten (constraint x) = constraint x
  flatten (ex q)         = ex (flatten q)
  flatten (ϕ and ψ)      = conj (flatten ϕ) (flatten ψ)
  flatten (ϕ or ψ)       = disj (flatten ϕ) (flatten ψ)

  flatten-ok : ∀ {Δ} (ϕ : Query Δ) η →
               eval-Query extFunc ϕ η ⇔ eval-FlatQuery (flatten ϕ) η
  flatten-ok (constraint x) η = ⇔-refl
  flatten-ok (ex ϕ) η = cong-∃ λ q → flatten-ok ϕ (extend-env η q)
  flatten-ok (ϕ and ψ) η =
    ⇔-trans (×-cong (flatten-ok ϕ η) (flatten-ok ψ η))
              (equi-conj (flatten ϕ) (flatten ψ) η)
  flatten-ok (ϕ or ψ) η =
    ⇔-trans (⊎-cong (flatten-ok ϕ η) (flatten-ok ψ η))
              (equi-disj (flatten ϕ) (flatten ψ) η)
