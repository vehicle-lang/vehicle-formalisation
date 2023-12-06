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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong₂; cong)
open import Util using (_<ᵇ_)
open import EquiInhabited

open import VerifierLang.Syntax

module VerifierLang.Semantics (extFunc : ℚ → ℚ) where

Env : LinVarCtxt → Set
Env Δ = Var Δ → ℚ

empty-env : Env ε
empty-env ()

extend-env : ∀ {Δ} → Env Δ → ℚ → Env (Δ ,∙)
extend-env η q zero     = q
extend-env η q (succ x) = η x

ℰ⟦_⟧ : ∀ {Δ} → LinExp Δ → Env Δ → ℚ
ℰ⟦ const q ⟧    η = q
ℰ⟦ q `*`var x ⟧ η = q * η x
ℰ⟦ e₁ `+` e₂ ⟧  η = ℰ⟦ e₁ ⟧ η + ℰ⟦ e₂ ⟧ η

eval-⊛ : ∀ {Δ} q (e : LinExp Δ) η → q * ℰ⟦ e ⟧ η ≡ ℰ⟦ q ⊛ e ⟧ η
eval-⊛ q (const x) η = refl
eval-⊛ q (r `*`var x) η = sym (*-assoc q r (η x))
eval-⊛ q (e₁ `+` e₂) η rewrite sym (eval-⊛ q e₁ η) rewrite sym (eval-⊛ q e₂ η) =
  *-distribˡ-+ q (ℰ⟦ e₁ ⟧ η) (ℰ⟦ e₂ ⟧ η)

𝒞⟦_⟧ : ∀ {Δ} → Constraint Δ → Env Δ → Bool
𝒞⟦ e₁ `≤` e₂ ⟧  η = ℰ⟦ e₁ ⟧ η ≤ᵇ ℰ⟦ e₂ ⟧ η
𝒞⟦ e₁ `<` e₂ ⟧  η = ℰ⟦ e₁ ⟧ η <ᵇ ℰ⟦ e₂ ⟧ η
𝒞⟦ e₁ `=` e₂ ⟧  η = (ℰ⟦ e₁ ⟧ η ≟ ℰ⟦ e₂ ⟧ η) .does
𝒞⟦ e₁ `≠` e₂ ⟧  η = not ((ℰ⟦ e₁ ⟧ η ≟ ℰ⟦ e₂ ⟧ η) .does)
𝒞⟦ p and q ⟧    η = 𝒞⟦ p ⟧ η ∧ 𝒞⟦ q ⟧ η
𝒞⟦ p or q ⟧     η = 𝒞⟦ p ⟧ η ∨ 𝒞⟦ q ⟧ η
𝒞⟦ x₁ `=`f x₂ ⟧ η = (η x₁ ≟ extFunc (η x₂)) .does
𝒞⟦ x₁ `≠`f x₂ ⟧ η = not ((η x₁ ≟ extFunc (η x₂)) .does)

eval-negate : ∀ {Δ} (p : Constraint Δ) η → not (𝒞⟦ p ⟧ η) ≡ 𝒞⟦ negate p ⟧ η
eval-negate (x `≤` x₁) η = refl
eval-negate (x `<` x₁) η = not-involutive _
eval-negate (x `=` x₁) η = refl
eval-negate (x `≠` x₁) η = not-involutive _
eval-negate (p and q)  η rewrite sym (eval-negate p η)
                         rewrite sym (eval-negate q η) =
                            deMorgan₁ (𝒞⟦ p ⟧ η) (𝒞⟦ q ⟧ η)
eval-negate (p or q)   η rewrite sym (eval-negate p η)
                         rewrite sym (eval-negate q η) =
                            deMorgan₂ (𝒞⟦ p ⟧ η) (𝒞⟦ q ⟧ η)
eval-negate (x₁ `=`f x₂) η = refl
eval-negate (x₁ `≠`f x₂) η = not-involutive _

eval-ExFormula : ∀ {Δ} → ExFormula Δ → Env Δ → Set
eval-ExFormula (constraint ϕ) η = True (𝒞⟦ ϕ ⟧ η)
eval-ExFormula (ex ϕ) η = Σ[ q ∈ ℚ ] eval-ExFormula ϕ (extend-env η q)
eval-ExFormula (ϕ and ψ) η = eval-ExFormula ϕ η × eval-ExFormula ψ η
eval-ExFormula (ϕ or ψ) η = eval-ExFormula ϕ η ⊎ eval-ExFormula ψ η

eval-PrenexFormula : ∀ {Δ} → PrenexFormula Δ → Env Δ → Set
eval-PrenexFormula (constraint ϕ) η = True (𝒞⟦ ϕ ⟧ η)
eval-PrenexFormula (ex ϕ) η = Σ[ q ∈ ℚ ] (eval-PrenexFormula ϕ (extend-env η q))

------------------------------------------------------------------------------
-- Evaluation contexts

record World : Set where
  field
    ctxt : LinVarCtxt
    env  : Env ctxt
open World public

empty : World
empty .ctxt = ε
empty .env = empty-env

-- World morphisms extend the context whilst making sure that the
-- environment is preserved.
record _⇒w_ (w₁ w₂ : World) : Set where
  field
    ren   : w₁ .ctxt ⇒ᵣ w₂ .ctxt
    presv : ∀ x → w₁ .env (ren x) ≡ w₂ .env x
open _⇒w_ public

id-w : ∀ {w} → w ⇒w w
id-w .ren x = x
id-w .presv x = refl

_∘w_ : ∀ {w₁ w₂ w₃} → w₂ ⇒w w₃ → w₁ ⇒w w₂ → w₁ ⇒w w₃
(f ∘w g) .ren x = g .ren (f .ren x)
(f ∘w g) .presv x = trans (g .presv (f .ren x)) (f .presv x)

extend-w : World → ℚ → World
extend-w w q .ctxt = w .ctxt ,∙
extend-w w q .env = extend-env (w .env) q

under-w : ∀ {w₁ w₂ q} → (w₁ ⇒w w₂) → (extend-w w₁ q ⇒w extend-w w₂ q)
under-w ρ .ren = under (ρ .ren)
under-w ρ .presv zero = refl
under-w ρ .presv (succ x) = ρ .presv x

under-w' : ∀ {w₁ w₂ q₁ q₂} → (q₁ ≡ q₂) → (w₁ ⇒w w₂) → (extend-w w₁ q₁ ⇒w extend-w w₂ q₂)
under-w' eq ρ .ren = under (ρ .ren)
under-w' eq ρ .presv zero = eq
under-w' eq ρ .presv (succ x) = ρ .presv x

wk-w : ∀ {w q} → extend-w w q ⇒w w
wk-w .ren = succ
wk-w .presv x = refl

------------------------------------------------------------------------------
-- Evaluation is preserved under extension of the evaluation context

ext-evalLinExp :
  ∀ {w₁ w₂} e (ρ : w₂ ⇒w w₁) →
    ℰ⟦ e ⟧ (w₁ .env) ≡ ℰ⟦ rename-LinExp (ρ .ren) e ⟧ (w₂ .env)
ext-evalLinExp (const q)    ρ = refl
ext-evalLinExp (q `*`var x) ρ = cong (λ □ → q * □) (sym (ρ .presv x))
ext-evalLinExp (e₁ `+` e₂)  ρ = cong₂ _+_ (ext-evalLinExp e₁ ρ) (ext-evalLinExp e₂ ρ)

ext-evalConstraint :
  ∀ {w₁ w₂} p (ρ : w₂ ⇒w w₁) →
    𝒞⟦ p ⟧ (w₁ .env) ≡ 𝒞⟦ rename-Constraint (ρ .ren) p ⟧ (w₂ .env)
ext-evalConstraint (e₁ `≤` e₂) ρ rewrite ext-evalLinExp e₁ ρ rewrite ext-evalLinExp e₂ ρ = refl
ext-evalConstraint (e₁ `<` e₂) ρ rewrite ext-evalLinExp e₁ ρ rewrite ext-evalLinExp e₂ ρ = refl
ext-evalConstraint (e₁ `=` e₂) ρ rewrite ext-evalLinExp e₁ ρ rewrite ext-evalLinExp e₂ ρ = refl
ext-evalConstraint (e₁ `≠` e₂) ρ rewrite ext-evalLinExp e₁ ρ rewrite ext-evalLinExp e₂ ρ = refl
ext-evalConstraint (p and q)   ρ rewrite ext-evalConstraint p ρ rewrite ext-evalConstraint q ρ = refl
ext-evalConstraint (p or q)    ρ rewrite ext-evalConstraint p ρ rewrite ext-evalConstraint q ρ = refl
ext-evalConstraint (x `=`f y)  ρ rewrite ρ .presv x rewrite ρ .presv y = refl
ext-evalConstraint (x `≠`f y)  ρ rewrite ρ .presv x rewrite ρ .presv y = refl

ext-PrenexFormula : ∀ {w₁ w₂} (ρ : w₂ ⇒w w₁) ϕ →
                eval-PrenexFormula ϕ (w₁ .env) ⇔
                   eval-PrenexFormula (rename-PrenexFormula (ρ .ren) ϕ) (w₂ .env)
ext-PrenexFormula ρ (constraint ϕ) = cong-True (ext-evalConstraint ϕ ρ)
ext-PrenexFormula ρ (ex ϕ) = cong-∃ λ q → ext-PrenexFormula (under-w ρ) ϕ

------------------------------------------------------------------------------
equi-conj-constraint : ∀ {Δ} (ϕ : Constraint Δ) ψ η →
                       (True (𝒞⟦ ϕ ⟧ η) × eval-PrenexFormula ψ η)
                          ⇔ eval-PrenexFormula (conj-constraint ϕ ψ) η
equi-conj-constraint ϕ (constraint x) η = True-∧
equi-conj-constraint ϕ (ex ψ) η =
  ⇔-trans
    and-comm-left
    (⇔-trans
     (cong-∃ λ q → ×-cong (cong-True (ext-evalConstraint ϕ wk-w)) ⇔-refl)
     (cong-∃ λ q →
        equi-conj-constraint (rename-Constraint succ ϕ) ψ (extend-env η q)))

equi-conj : ∀ {Δ} (ϕ : PrenexFormula Δ) ψ η →
            (eval-PrenexFormula ϕ η × eval-PrenexFormula ψ η) ⇔ eval-PrenexFormula (conj ϕ ψ) η
equi-conj (constraint ϕ) ψ η = equi-conj-constraint ϕ ψ η
equi-conj (ex ϕ) ψ η =
  ⇔-trans
   and-comm-right
   (cong-∃ λ q →
    ⇔-trans
     (×-cong ⇔-refl (ext-PrenexFormula wk-w ψ))
     (equi-conj ϕ (rename-PrenexFormula succ ψ) (extend-env η q)))

equi-disj-constraint : ∀ {Δ} (ϕ : Constraint Δ) ψ η →
                       (True (𝒞⟦ ϕ ⟧ η) ⊎ eval-PrenexFormula ψ η)
                          ⇔ eval-PrenexFormula (disj-constraint ϕ ψ) η
equi-disj-constraint ϕ (constraint x) η = True-∨
equi-disj-constraint ϕ (ex ψ) η =
  ⇔-trans
   (or-comm-right 1ℚ)
   (cong-∃
    λ q → ⇔-trans
           (⊎-cong (cong-True (ext-evalConstraint ϕ wk-w)) ⇔-refl)
           (equi-disj-constraint (rename-Constraint succ ϕ) ψ (extend-env η q)))

equi-disj : ∀ {Δ} (ϕ : PrenexFormula Δ) ψ η →
            (eval-PrenexFormula ϕ η ⊎ eval-PrenexFormula ψ η) ⇔ eval-PrenexFormula (disj ϕ ψ) η
equi-disj (constraint ϕ) ψ η = equi-disj-constraint ϕ ψ η
equi-disj (ex ϕ) ψ η =
  ⇔-trans (or-comm-left 1ℚ)
   (cong-∃ λ q →
    ⇔-trans
     (⊎-cong ⇔-refl (ext-PrenexFormula wk-w ψ))
     (equi-disj ϕ (rename-PrenexFormula succ ψ) (extend-env η q)))

toPrenexForm-ok : ∀ {Δ} (ϕ : ExFormula Δ) η →
             eval-ExFormula ϕ η ⇔ eval-PrenexFormula (toPrenexForm ϕ) η
toPrenexForm-ok (constraint x) η = ⇔-refl
toPrenexForm-ok (ex ϕ) η = cong-∃ λ q → toPrenexForm-ok ϕ (extend-env η q)
toPrenexForm-ok (ϕ and ψ) η =
  ⇔-trans (×-cong (toPrenexForm-ok ϕ η) (toPrenexForm-ok ψ η))
            (equi-conj (toPrenexForm ϕ) (toPrenexForm ψ) η)
toPrenexForm-ok (ϕ or ψ) η =
  ⇔-trans (⊎-cong (toPrenexForm-ok ϕ η) (toPrenexForm-ok ψ η))
            (equi-disj (toPrenexForm ϕ) (toPrenexForm ψ) η)
