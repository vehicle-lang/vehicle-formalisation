{-# OPTIONS --safe #-}

module VerifierLang.Syntax where

open import Data.Rational as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong₂)

------------------------------------------------------------------------------
-- Linear variable contexts and renaming

data LinVarCtxt : Set where
  ε   : LinVarCtxt
  _,∙ : LinVarCtxt → LinVarCtxt

data Var : LinVarCtxt → Set where
  zero : ∀ {Δ} → Var (Δ ,∙)
  succ : ∀ {Δ} → Var Δ → Var (Δ ,∙)

_⇒ᵣ_ : LinVarCtxt → LinVarCtxt → Set
Δ₁ ⇒ᵣ Δ₂ = Var Δ₂ → Var Δ₁

_∘_ : ∀ {Δ₁ Δ₂ Δ₃} → Δ₂ ⇒ᵣ Δ₃ → Δ₁ ⇒ᵣ Δ₂ → Δ₁ ⇒ᵣ Δ₃
ρ ∘ ρ' = λ z → ρ' (ρ z)

under : ∀ {Δ Δ'} → Δ ⇒ᵣ Δ' → (Δ ,∙) ⇒ᵣ (Δ' ,∙)
under ρ zero     = zero
under ρ (succ x) = succ (ρ x)

wk-r : ∀ {Δ} → (Δ ,∙) ⇒ᵣ Δ
wk-r = succ

Renameable : (LinVarCtxt → Set) → Set
Renameable A = ∀ {Δ Δ'} → (Δ ⇒ᵣ Δ') → A Δ' → A Δ

-- FIXME: this is a generic definition for any presheaves
_⇒ₖ_ : (LinVarCtxt → Set) → (LinVarCtxt → Set) → LinVarCtxt → Set
(X ⇒ₖ Y) Δ = ∀ Δ' → Δ' ⇒ᵣ Δ → X Δ' → Y Δ'

rename-⇒ₖ : ∀ {X Y} → Renameable (X ⇒ₖ Y)
rename-⇒ₖ ρ f _ ρ' = f _ (λ v → ρ' (ρ v))

------------------------------------------------------------------------------
-- Linear and Constraint Expressions in negation normal form

data LinExp (Δ : LinVarCtxt) : Set where
  const : ℚ → LinExp Δ
  var   : ℚ → Var Δ → LinExp Δ --- FIXME: rename to _`*`var_
  _`+`_ : LinExp Δ → LinExp Δ → LinExp Δ

data Constraint (Δ : LinVarCtxt) : Set where
  _`≤`_ : LinExp Δ → LinExp Δ → Constraint Δ
  _`<`_ : LinExp Δ → LinExp Δ → Constraint Δ
  _`=`_ : LinExp Δ → LinExp Δ → Constraint Δ
  _`≠`_ : LinExp Δ → LinExp Δ → Constraint Δ
  _`=`f_ : Var Δ → Var Δ → Constraint Δ
  _`≠`f_ : Var Δ → Var Δ → Constraint Δ
  _and_ : Constraint Δ → Constraint Δ → Constraint Δ
  _or_  : Constraint Δ → Constraint Δ → Constraint Δ

rename-LinExp : Renameable LinExp
rename-LinExp ρ (const q)   = const q
rename-LinExp ρ (var r x)   = var r (ρ x)
rename-LinExp ρ (e₁ `+` e₂) = (rename-LinExp ρ e₁) `+` (rename-LinExp ρ e₂)

rename-Constraint : Renameable Constraint
rename-Constraint ρ (e₁ `≤` e₂) = rename-LinExp ρ e₁ `≤` rename-LinExp ρ e₂
rename-Constraint ρ (e₁ `<` e₂) = rename-LinExp ρ e₁ `<` rename-LinExp ρ e₂
rename-Constraint ρ (p and q)   = (rename-Constraint ρ p) and (rename-Constraint ρ q)
rename-Constraint ρ (p or q)    = (rename-Constraint ρ p) or (rename-Constraint ρ q)
rename-Constraint ρ (e₁ `=` e₂) = rename-LinExp ρ e₁ `=` rename-LinExp ρ e₂
rename-Constraint ρ (e₁ `≠` e₂) = rename-LinExp ρ e₁ `≠` rename-LinExp ρ e₂
rename-Constraint ρ (x₁ `=`f x₂) = ρ x₁ `=`f ρ x₂
rename-Constraint ρ (x₁ `≠`f x₂) = ρ x₁ `≠`f ρ x₂

------------------------------------------------------------------------------
-- Operations

_⊛_ : ∀ {Δ} → ℚ → LinExp Δ → LinExp Δ
q ⊛ const x     = const (q ℚ.* x)
q ⊛ var r v     = var (q ℚ.* r) v
q ⊛ (e₁ `+` e₂) = (q ⊛ e₁) `+` (q ⊛ e₂)

negate : ∀ {Δ} → Constraint Δ → Constraint Δ
negate (e₁ `≤` e₂) = e₂ `<` e₁
negate (e₁ `<` e₂) = e₂ `≤` e₁
negate (p and q) = negate p or negate q
negate (p or q) = negate p and negate q
negate (e₁ `=` e₂) = e₁ `≠` e₂
negate (e₁ `≠` e₂) = e₁ `=` e₂
negate (x₁ `=`f x₂) = x₁ `≠`f x₂
negate (x₁ `≠`f x₂) = x₁ `=`f x₂

-- Negation commutes with renaming
rename-negate : ∀ {Δ' Δ} (ρ : Δ' ⇒ᵣ Δ) (ϕ : Constraint Δ)  →
                rename-Constraint ρ (negate ϕ) ≡ negate (rename-Constraint ρ ϕ)
rename-negate ρ (x `≤` x₁) = refl
rename-negate ρ (x `<` x₁) = refl
rename-negate ρ (x `=` x₁) = refl
rename-negate ρ (x `≠` x₁) = refl
rename-negate ρ (x `=`f x₁) = refl
rename-negate ρ (x `≠`f x₁) = refl
rename-negate ρ (ϕ and ϕ₁) = cong₂ _or_ (rename-negate ρ ϕ) (rename-negate ρ ϕ₁)
rename-negate ρ (ϕ or ϕ₁) = cong₂ _and_ (rename-negate ρ ϕ) (rename-negate ρ ϕ₁)

------------------------------------------------------------------------------
-- Quantification, first via "free form" formulas with existential
-- quantifiers in them.

data ExFormula : LinVarCtxt → Set where
  constraint : ∀ {Δ} → Constraint Δ → ExFormula Δ
  ex         : ∀ {Δ} → ExFormula (Δ ,∙) → ExFormula Δ
  _and_      : ∀ {Δ} → ExFormula Δ → ExFormula Δ → ExFormula Δ
  _or_       : ∀ {Δ} → ExFormula Δ → ExFormula Δ → ExFormula Δ

rename-ExFormula : Renameable ExFormula
rename-ExFormula ρ (constraint ϕ) = constraint (rename-Constraint ρ ϕ)
rename-ExFormula ρ (ex ϕ)         = ex (rename-ExFormula (under ρ) ϕ)
rename-ExFormula ρ (ϕ and ψ)      = rename-ExFormula ρ ϕ and rename-ExFormula ρ ψ
rename-ExFormula ρ (ϕ or ψ)       = rename-ExFormula ρ ϕ or rename-ExFormula ρ ψ

------------------------------------------------------------------------------
-- Formulas where all existential quantifiers are floated out to the
-- front.

data PrenexFormula : LinVarCtxt → Set where
  constraint : ∀ {Δ} → Constraint Δ → PrenexFormula Δ
  ex         : ∀ {Δ} → PrenexFormula (Δ ,∙) → PrenexFormula Δ

rename-PrenexFormula : ∀ {Δ Δ'} → (ρ : Δ' ⇒ᵣ Δ) → PrenexFormula Δ → PrenexFormula Δ'
rename-PrenexFormula ρ (constraint x) = constraint (rename-Constraint ρ x)
rename-PrenexFormula ρ (ex ϕ) = ex (rename-PrenexFormula (under ρ) ϕ)

conj-constraint : ∀ {Δ} → Constraint Δ → PrenexFormula Δ → PrenexFormula Δ
conj-constraint ϕ (constraint ψ) = constraint (ϕ and ψ)
conj-constraint ϕ (ex ψ) = ex (conj-constraint (rename-Constraint succ ϕ) ψ)

conj : ∀ {Δ} → PrenexFormula Δ → PrenexFormula Δ → PrenexFormula Δ
conj (constraint ϕ) ψ = conj-constraint ϕ ψ
conj (ex ϕ)         ψ = ex (conj ϕ (rename-PrenexFormula succ ψ))

disj-constraint : ∀ {Δ} → Constraint Δ → PrenexFormula Δ → PrenexFormula Δ
disj-constraint ϕ (constraint ψ) = constraint (ϕ or ψ)
disj-constraint ϕ (ex ψ) = ex (disj-constraint (rename-Constraint succ ϕ) ψ)

disj : ∀ {Δ} → PrenexFormula Δ → PrenexFormula Δ → PrenexFormula Δ
disj (constraint ϕ) ψ = disj-constraint ϕ ψ
disj (ex ϕ) ψ = ex (disj ϕ (rename-PrenexFormula succ ψ))

toPrenexForm : ∀ {Δ} → ExFormula Δ → PrenexFormula Δ
toPrenexForm (constraint x) = constraint x
toPrenexForm (ex q)         = ex (toPrenexForm q)
toPrenexForm (ϕ and ψ)      = conj (toPrenexForm ϕ) (toPrenexForm ψ)
toPrenexForm (ϕ or ψ)       = disj (toPrenexForm ϕ) (toPrenexForm ψ)
