{-# OPTIONS --postfix-projections #-}

module Expansion where

open import Data.Bool renaming (T to True)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Rational using (ℚ; 1ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; cong)

open import NormalisedExpr
open import NormalisationCorrect
open import Isomorphism

module _ where

  variable
    A B : Set
    P : A → Set
    Q : B → Set

  comm : (Σ[ a ∈ A ] P a) × (Σ[ b ∈ B ] Q b) → Σ[ a ∈ A ] Σ[ b ∈ B ] (P a × Q b)
  comm ((a , p) , (b , q)) = a , b , p , q

  comm' : Σ[ a ∈ A ] Σ[ b ∈ B ] (P a × Q b) → (Σ[ a ∈ A ] P a) × (Σ[ b ∈ B ] Q b)
  comm' (a , b , p , q) = ((a , p) , (b , q))

  module _ (a : A)(b : B) where

    comm2 : (Σ[ a ∈ A ] P a) ⊎ (Σ[ b ∈ B ] Q b) → Σ[ a ∈ A ] Σ[ b ∈ B ] (P a ⊎ Q b)
    comm2 (inj₁ (a , p)) = a , b , inj₁ p
    comm2 (inj₂ (b , q)) = a , b , inj₂ q

    comm2' : Σ[ a ∈ A ] Σ[ b ∈ B ] (P a ⊎ Q b) → (Σ[ a ∈ A ] P a) ⊎ (Σ[ b ∈ B ] Q b)
    comm2' (a , b , inj₁ p) = inj₁ (a , p)
    comm2' (a , b , inj₂ q) = inj₂ (b , q)

  move-in : (A × Σ[ b ∈ B ] Q b) ↔ (Σ[ b ∈ B ] (A × Q b))
  move-in .fwd (a , b , q) = b , a , q
  move-in .bwd (b , a , q) = a , b , q

  and-comm-right : ((Σ[ a ∈ A ] P a) × B) ↔ (Σ[ a ∈ A ] (P a × B))
  and-comm-right .fwd ((a , p) , b) = a , p , b
  and-comm-right .bwd (a , p , b) = (a , p) , b

  or-comm-right : B → (A ⊎ Σ[ b ∈ B ] Q b) ↔ (Σ[ b ∈ B ] (A ⊎ Q b))
  or-comm-right b .fwd (inj₁ a) = b , inj₁ a
  or-comm-right b .fwd (inj₂ (b' , q)) = b' , inj₂ q
  or-comm-right b .bwd (b' , inj₁ a) = inj₁ a
  or-comm-right b .bwd (b' , inj₂ q) = inj₂ (b' , q)

  or-comm-left : A → ((Σ[ a ∈ A ] P a) ⊎ B) ↔ (Σ[ a ∈ A ] (P a ⊎ B))
  or-comm-left a₀ .fwd (inj₁ (a , p)) = a , inj₁ p
  or-comm-left a₀ .fwd (inj₂ b)       = a₀ , inj₂ b
  or-comm-left a₀ .bwd (a , inj₁ p) = inj₁ (a , p)
  or-comm-left a₀ .bwd (a , inj₂ b) = inj₂ b

data FlatQuery : LinVarCtxt → Set where
  constraint : ∀ {Δ} → ConstraintExp Δ → FlatQuery Δ
  ex         : ∀ {Δ} → FlatQuery (Δ ,∙) → FlatQuery Δ

rename-FlatQuery : ∀ {Δ Δ'} → (ρ : Δ' ⇒ᵣ Δ) → FlatQuery Δ → FlatQuery Δ'
rename-FlatQuery ρ (constraint x) = constraint (rename-ConstraintExp ρ x)
rename-FlatQuery ρ (ex ϕ) = ex (rename-FlatQuery (under ρ) ϕ)

module _ (extFunc : ℚ → ℚ) where

  eval-FlatQuery : ∀ {Δ} → FlatQuery Δ → Env Δ → Set
  eval-FlatQuery (constraint ϕ) η = True (eval-ConstraintExp extFunc ϕ η)
  eval-FlatQuery (ex ϕ) η = Σ[ q ∈ ℚ ] (eval-FlatQuery ϕ (extend-env η q))

  ext-FlatQuery : ∀ {w₁ w₂} (ρ : w₂ ⇒w w₁) ϕ →
                  eval-FlatQuery ϕ (w₁ .env) ↔
                     eval-FlatQuery (rename-FlatQuery (ρ .ren) ϕ) (w₂ .env)
  ext-FlatQuery ρ (constraint ϕ) = cong-True (ext-evalConstraint extFunc ϕ ρ)
  ext-FlatQuery ρ (ex ϕ) = cong-Σ-snd λ q → ext-FlatQuery (under-w ρ) ϕ

  conj-constraint : ∀ {Δ} → ConstraintExp Δ → FlatQuery Δ → FlatQuery Δ
  conj-constraint ϕ (constraint ψ) = constraint (ϕ and ψ)
  conj-constraint ϕ (ex ψ) = ex (conj-constraint (rename-ConstraintExp succ ϕ) ψ)

  equi-conj-constraint : ∀ {Δ} (ϕ : ConstraintExp Δ) ψ η →
                         (True (eval-ConstraintExp extFunc ϕ η) × eval-FlatQuery ψ η)
                            ↔ eval-FlatQuery (conj-constraint ϕ ψ) η
  equi-conj-constraint ϕ (constraint x) η = True-∧
  equi-conj-constraint ϕ (ex ψ) η =
    ↔-trans
      move-in
      (↔-trans
       (cong-Σ-snd (λ q → ×-cong (cong-True (ext-evalConstraint extFunc ϕ wk-w)) ↔-refl))
       (cong-Σ-snd (λ q →
          equi-conj-constraint (rename-ConstraintExp succ ϕ) ψ (extend-env η q))))

  conj : ∀ {Δ} → FlatQuery Δ → FlatQuery Δ → FlatQuery Δ
  conj (constraint ϕ) ψ = conj-constraint ϕ ψ
  conj (ex ϕ)         ψ = ex (conj ϕ (rename-FlatQuery succ ψ))

  equi-conj : ∀ {Δ} (ϕ : FlatQuery Δ) ψ η →
              (eval-FlatQuery ϕ η × eval-FlatQuery ψ η) ↔ eval-FlatQuery (conj ϕ ψ) η
  equi-conj (constraint ϕ) ψ η = equi-conj-constraint ϕ ψ η
  equi-conj (ex ϕ) ψ η =
    ↔-trans
     and-comm-right
     (cong-Σ-snd λ q →
      ↔-trans
       (×-cong ↔-refl (ext-FlatQuery wk-w ψ))
       (equi-conj ϕ (rename-FlatQuery succ ψ) (extend-env η q)))

  disj-constraint : ∀ {Δ} → ConstraintExp Δ → FlatQuery Δ → FlatQuery Δ
  disj-constraint ϕ (constraint ψ) = constraint (ϕ or ψ)
  disj-constraint ϕ (ex ψ) = ex (disj-constraint (rename-ConstraintExp succ ϕ) ψ)

  disj : ∀ {Δ} → FlatQuery Δ → FlatQuery Δ → FlatQuery Δ
  disj (constraint ϕ) ψ = disj-constraint ϕ ψ
  disj (ex ϕ) ψ = ex (disj ϕ (rename-FlatQuery succ ψ))

  equi-disj-constraint : ∀ {Δ} (ϕ : ConstraintExp Δ) ψ η →
                         (True (eval-ConstraintExp extFunc ϕ η) ⊎ eval-FlatQuery ψ η)
                            ↔ eval-FlatQuery (disj-constraint ϕ ψ) η
  equi-disj-constraint ϕ (constraint x) η = True-∨
  equi-disj-constraint ϕ (ex ψ) η =
    ↔-trans
     (or-comm-right 1ℚ)
     (cong-Σ-snd
      λ q → ↔-trans
             (⊎-cong (cong-True (ext-evalConstraint extFunc ϕ wk-w)) ↔-refl)
             (equi-disj-constraint (rename-ConstraintExp succ ϕ) ψ (extend-env η q)))

  equi-disj : ∀ {Δ} (ϕ : FlatQuery Δ) ψ η →
              (eval-FlatQuery ϕ η ⊎ eval-FlatQuery ψ η) ↔ eval-FlatQuery (disj ϕ ψ) η
  equi-disj (constraint ϕ) ψ η = equi-disj-constraint ϕ ψ η
  equi-disj (ex ϕ) ψ η =
    ↔-trans (or-comm-left 1ℚ)
     (cong-Σ-snd λ q →
      ↔-trans
       (⊎-cong ↔-refl (ext-FlatQuery wk-w ψ))
       (equi-disj ϕ (rename-FlatQuery succ ψ) (extend-env η q)))

  flatten : ∀ {Δ} → Query Δ → FlatQuery Δ
  flatten (constraint x) = constraint x
  flatten (ex q)         = ex (flatten q)
  flatten (ϕ and ψ)      = conj (flatten ϕ) (flatten ψ)
  flatten (ϕ or ψ)       = disj (flatten ϕ) (flatten ψ)

  flatten-ok : ∀ {Δ} (ϕ : Query Δ) η →
               eval-Query extFunc ϕ η ↔ eval-FlatQuery (flatten ϕ) η
  flatten-ok (constraint x) η = ↔-refl
  flatten-ok (ex ϕ) η = cong-Σ-snd λ q → flatten-ok ϕ (extend-env η q)
  flatten-ok (ϕ and ψ) η = ↔-trans (×-cong (flatten-ok ϕ η) (flatten-ok ψ η)) (equi-conj (flatten ϕ) (flatten ψ) η)
  flatten-ok (ϕ or ψ) η = ↔-trans (⊎-cong (flatten-ok ϕ η) (flatten-ok ψ η)) (equi-disj (flatten ϕ) (flatten ψ) η)
