{-# OPTIONS --safe #-}

open import Data.Bool
       using (Bool; true; false; _∧_; _∨_; if_then_else_; not)
       renaming (T to True)
open import Data.Bool.Properties using (not-involutive; ∨-∧-booleanAlgebra)
open import Algebra.Lattice.Properties.BooleanAlgebra ∨-∧-booleanAlgebra using (deMorgan₁; deMorgan₂)
open import Data.Product using (Σ-syntax; _×_)
open import Data.Sum using (_⊎_)
open import Data.Rational as ℚ using (ℚ; 1ℚ; _*_; _+_; _≤ᵇ_; _≟_)
open import Data.Rational.Properties using (*-assoc; *-distribˡ-+)
open import Function.Base using (id)
open import Relation.Nullary using (¬_; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong₂; cong)
open import Util using (_<ᵇ_)
open import Util.EquiInhabited

open import VerifierLang.Syntax

module VerifierLang.Semantics (extFunc : ℚ → ℚ) where

------------------------------------------------------------------------------
-- Environments in which evaluation is performed

Env : LinVarCtxt → Set
Env Δ = Var Δ → ℚ

empty-env : Env ε
empty-env ()

extend-env : ∀ {Δ} → Env Δ → ℚ → Env (Δ ,∙)
extend-env η q zero     = q
extend-env η q (succ x) = η x

------------------------------------------------------------------------------
-- Evaluation of linear expressions

ℰ⟦_⟧ : ∀ {Δ} → LinExp Δ → Env Δ → ℚ
ℰ⟦ const q ⟧    η = q
ℰ⟦ q `*`var x ⟧ η = q * η x
ℰ⟦ e₁ `+` e₂ ⟧  η = ℰ⟦ e₁ ⟧ η + ℰ⟦ e₂ ⟧ η

------------------------------------------------------------------------------
-- Evaluation of constraints

𝒞⟦_⟧ : ∀ {Δ} → Constraint Δ → Env Δ → Bool
𝒞⟦ e₁ `≤` e₂ ⟧  η = ℰ⟦ e₁ ⟧ η ≤ᵇ ℰ⟦ e₂ ⟧ η
𝒞⟦ e₁ `<` e₂ ⟧  η = ℰ⟦ e₁ ⟧ η <ᵇ ℰ⟦ e₂ ⟧ η
𝒞⟦ e₁ `=` e₂ ⟧  η = (ℰ⟦ e₁ ⟧ η ≟ ℰ⟦ e₂ ⟧ η) .does
𝒞⟦ e₁ `≠` e₂ ⟧  η = not ((ℰ⟦ e₁ ⟧ η ≟ ℰ⟦ e₂ ⟧ η) .does)
𝒞⟦ x₁ `=`f x₂ ⟧ η = (η x₁ ≟ extFunc (η x₂)) .does
𝒞⟦ x₁ `≠`f x₂ ⟧ η = not ((η x₁ ≟ extFunc (η x₂)) .does)

------------------------------------------------------------------------------
-- Evaluation of query bodies

eval-QueryBody : ∀ {Δ} → QueryBody Δ → Env Δ → Bool
eval-QueryBody (constraint ϕ) η = 𝒞⟦ ϕ ⟧ η
eval-QueryBody (ϕ₁ and ϕ₂)    η = eval-QueryBody ϕ₁ η ∧ eval-QueryBody ϕ₂ η

------------------------------------------------------------------------------
-- Evaluation of constraints

eval-Query : ∀ {Δ} → Query Δ → Env Δ → Set
eval-Query (body ϕ) η = True (eval-QueryBody ϕ η)
eval-Query (ex ϕ) η = Σ[ q ∈ ℚ ] (eval-Query ϕ (extend-env η q))

eval-QuerySet : ∀ {Δ} → QuerySet Δ → Env Δ → Set
eval-QuerySet (query x) η = eval-Query x η
eval-QuerySet (ϕ or ϕ₂) η = eval-QuerySet ϕ η ⊎ eval-QuerySet ϕ₂ η

eval-QueryTree : QueryTree → Set
eval-QueryTree (querySet negated x₁) = (if negated then ¬_ else id) (eval-QuerySet x₁ empty-env)
eval-QueryTree (t or t₁) = eval-QueryTree t ⊎ eval-QueryTree t₁
eval-QueryTree (t and t₁) = eval-QueryTree t × eval-QueryTree t₁

eval-⊛ : ∀ {Δ} q (e : LinExp Δ) η → q * ℰ⟦ e ⟧ η ≡ ℰ⟦ q ⊛ e ⟧ η
eval-⊛ q (const x) η = refl
eval-⊛ q (r `*`var x) η = sym (*-assoc q r (η x))
eval-⊛ q (e₁ `+` e₂) η rewrite sym (eval-⊛ q e₁ η) rewrite sym (eval-⊛ q e₂ η) =
  *-distribˡ-+ q (ℰ⟦ e₁ ⟧ η) (ℰ⟦ e₂ ⟧ η)

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
ext-evalConstraint (e₁ `≤` e₂) ρ rewrite ext-evalLinExp e₁ ρ | ext-evalLinExp e₂ ρ = refl
ext-evalConstraint (e₁ `<` e₂) ρ rewrite ext-evalLinExp e₁ ρ | ext-evalLinExp e₂ ρ = refl
ext-evalConstraint (e₁ `=` e₂) ρ rewrite ext-evalLinExp e₁ ρ | ext-evalLinExp e₂ ρ = refl
ext-evalConstraint (e₁ `≠` e₂) ρ rewrite ext-evalLinExp e₁ ρ | ext-evalLinExp e₂ ρ = refl
ext-evalConstraint (x `=`f y)  ρ rewrite ρ .presv x | ρ .presv y = refl
ext-evalConstraint (x `≠`f y)  ρ rewrite ρ .presv x | ρ .presv y = refl

ext-evalQueryBody : 
  ∀ {w₁ w₂} ϕ (ρ : w₂ ⇒w w₁) →
    eval-QueryBody ϕ (w₁ .env) ≡ eval-QueryBody (rename-QueryBody (ρ .ren) ϕ) (w₂ .env)
ext-evalQueryBody (constraint ϕ) ρ rewrite ext-evalConstraint ϕ ρ = refl
ext-evalQueryBody (ϕ₁ and ϕ₂)    ρ rewrite ext-evalQueryBody ϕ₁ ρ | ext-evalQueryBody ϕ₂ ρ = refl

ext-evalQuery : ∀ {w₁ w₂} (ρ : w₂ ⇒w w₁) ϕ →
                eval-Query ϕ (w₁ .env) ⇔
                   eval-Query (rename-Query (ρ .ren) ϕ) (w₂ .env)
ext-evalQuery ρ (body ϕ) = cong-True (ext-evalQueryBody ϕ ρ)
ext-evalQuery ρ (ex ϕ) = cong-∃ λ q → ext-evalQuery (under-w ρ) ϕ
