{-# OPTIONS --safe #-}

module VerifierLang.Syntax where

open import Data.Bool using (Bool)
open import Data.Rational as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong₂)

------------------------------------------------------------------------------
-- Linear variable contexts and renaming

data LinVarCtxt : Set where
  ε   : LinVarCtxt
  _,∙ : LinVarCtxt → LinVarCtxt

private
  variable
    Δ Δ₁ Δ₂ Δ₃ : LinVarCtxt

data Var : LinVarCtxt → Set where
  zero : ∀ {Δ} → Var (Δ ,∙)
  succ : ∀ {Δ} → Var Δ → Var (Δ ,∙)

_⇒ᵣ_ : LinVarCtxt → LinVarCtxt → Set
Δ₁ ⇒ᵣ Δ₂ = Var Δ₂ → Var Δ₁

_∘_ : Δ₂ ⇒ᵣ Δ₃ → Δ₁ ⇒ᵣ Δ₂ → Δ₁ ⇒ᵣ Δ₃
ρ ∘ ρ' = λ z → ρ' (ρ z)

under : Δ₁ ⇒ᵣ Δ₂ → (Δ₁ ,∙) ⇒ᵣ (Δ₂ ,∙)
under ρ zero     = zero
under ρ (succ x) = succ (ρ x)

wk-r : (Δ ,∙) ⇒ᵣ Δ
wk-r = succ

Renameable : (LinVarCtxt → Set) → Set
Renameable A = ∀ {Δ Δ'} → (Δ ⇒ᵣ Δ') → A Δ' → A Δ

-- FIXME: this is a generic definition for any presheaves
_⇒ₖ_ : (LinVarCtxt → Set) → (LinVarCtxt → Set) → LinVarCtxt → Set
(X ⇒ₖ Y) Δ = ∀ Δ' → Δ' ⇒ᵣ Δ → X Δ' → Y Δ'

rename-⇒ₖ : ∀ {X Y} → Renameable (X ⇒ₖ Y)
rename-⇒ₖ ρ f _ ρ' = f _ (λ v → ρ' (ρ v))

------------------------------------------------------------------------------
-- Linear Expressions

data LinExp (Δ : LinVarCtxt) : Set where
  const    : ℚ → LinExp Δ
  _`*`var_ : ℚ → Var Δ → LinExp Δ
  _`+`_    : LinExp Δ → LinExp Δ → LinExp Δ

rename-LinExp : Renameable LinExp
rename-LinExp ρ (const q)   = const q
rename-LinExp ρ (r `*`var x)   = r `*`var (ρ x)
rename-LinExp ρ (e₁ `+` e₂) = (rename-LinExp ρ e₁) `+` (rename-LinExp ρ e₂)

-- Scaling a linear expression
_⊛_ : ℚ → LinExp Δ → LinExp Δ
q ⊛ const x      = const (q ℚ.* x)
q ⊛ (r `*`var v) = (q ℚ.* r) `*`var v
q ⊛ (e₁ `+` e₂)  = (q ⊛ e₁) `+` (q ⊛ e₂)

------------------------------------------------------------------------------
-- Linear Constraints in negation normal form

data Constraint (Δ : LinVarCtxt) : Set where
  _`≤`_ : LinExp Δ → LinExp Δ → Constraint Δ
  _`<`_ : LinExp Δ → LinExp Δ → Constraint Δ
  _`=`_ : LinExp Δ → LinExp Δ → Constraint Δ
  _`≠`_ : LinExp Δ → LinExp Δ → Constraint Δ
  _`=`f_ : Var Δ → Var Δ → Constraint Δ
  _`≠`f_ : Var Δ → Var Δ → Constraint Δ
  
rename-Constraint : Renameable Constraint
rename-Constraint ρ (e₁ `≤` e₂) = rename-LinExp ρ e₁ `≤` rename-LinExp ρ e₂
rename-Constraint ρ (e₁ `<` e₂) = rename-LinExp ρ e₁ `<` rename-LinExp ρ e₂
rename-Constraint ρ (e₁ `=` e₂) = rename-LinExp ρ e₁ `=` rename-LinExp ρ e₂
rename-Constraint ρ (e₁ `≠` e₂) = rename-LinExp ρ e₁ `≠` rename-LinExp ρ e₂
rename-Constraint ρ (x₁ `=`f x₂) = ρ x₁ `=`f ρ x₂
rename-Constraint ρ (x₁ `≠`f x₂) = ρ x₁ `≠`f ρ x₂

negate : Constraint Δ → Constraint Δ
negate (e₁ `≤` e₂) = e₂ `<` e₁
negate (e₁ `<` e₂) = e₂ `≤` e₁
negate (e₁ `=` e₂) = e₁ `≠` e₂
negate (e₁ `≠` e₂) = e₁ `=` e₂
negate (x₁ `=`f x₂) = x₁ `≠`f x₂
negate (x₁ `≠`f x₂) = x₁ `=`f x₂

-- Negation commutes with renaming
rename-negate : (ρ : Δ₁ ⇒ᵣ Δ₂) (ϕ : Constraint Δ₂)  →
                rename-Constraint ρ (negate ϕ) ≡ negate (rename-Constraint ρ ϕ)
rename-negate ρ (e₁ `≤` e₂) = refl
rename-negate ρ (e₁ `<` e₂) = refl
rename-negate ρ (e₁ `=` e₂) = refl
rename-negate ρ (e₁ `≠` e₂) = refl
rename-negate ρ (x `=`f x₁) = refl
rename-negate ρ (x `≠`f x₁) = refl

------------------------------------------------------------------------------
-- Query body

data QueryBody (Δ : LinVarCtxt) : Set where
  constraint : Constraint Δ → QueryBody Δ
  _and_ : QueryBody Δ → QueryBody Δ → QueryBody Δ

rename-QueryBody : (ρ : Δ₁ ⇒ᵣ Δ₂) → QueryBody Δ₂ → QueryBody Δ₁
rename-QueryBody ρ (constraint x) = constraint (rename-Constraint ρ x)
rename-QueryBody ρ (ϕ₁ and ϕ₂) = rename-QueryBody ρ ϕ₁ and rename-QueryBody ρ ϕ₂

------------------------------------------------------------------------------
-- Formulas where all existential quantifiers are floated out to the
-- front.

data Query : LinVarCtxt → Set where
  body : ∀ {Δ} → QueryBody Δ → Query Δ
  ex   : ∀ {Δ} → Query (Δ ,∙) → Query Δ

rename-Query : ∀ {Δ Δ'} → (ρ : Δ' ⇒ᵣ Δ) → Query Δ → Query Δ'
rename-Query ρ (body x) = body (rename-QueryBody ρ x)
rename-Query ρ (ex ϕ) = ex (rename-Query (under ρ) ϕ)

------------------------------------------------------------------------------
-- A set of queries that are under the same variables

data QuerySet (Δ : LinVarCtxt) : Set where
  query : Query Δ → QuerySet Δ
  _or_ : QuerySet Δ → QuerySet Δ → QuerySet Δ

------------------------------------------------------------------------------
-- A tree of queries

data QueryTree : Set where
  querySet : Bool → QuerySet ε → QueryTree
  _or_ : QueryTree → QueryTree → QueryTree
  _and_ : QueryTree → QueryTree → QueryTree
