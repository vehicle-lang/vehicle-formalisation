{-# OPTIONS --postfix-projections --safe #-}

module NormalisedExpr where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; if_then_else_; not)
open import Data.Bool.Properties using (not-involutive)
open import Algebra.Properties.BooleanAlgebra (Data.Bool.Properties.∨-∧-booleanAlgebra) using (deMorgan₁; deMorgan₂)
open import Data.Product using (Σ-syntax)
open import Data.Rational as ℚ using (ℚ; 1ℚ; _*_; _+_; _≤ᵇ_; _≟_)
open import Data.Rational.Properties using (*-assoc; *-distribˡ-+)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

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

-- FIXME: make a Renameable record to combine the family and the
-- Renameable part

Renameable : (LinVarCtxt → Set) → Set
Renameable A = ∀ {Δ Δ'} → (Δ ⇒ᵣ Δ') → A Δ' → A Δ

_⇒ₖ_ : (LinVarCtxt → Set) → (LinVarCtxt → Set) → LinVarCtxt → Set
(X ⇒ₖ Y) Δ = ∀ Δ' → Δ' ⇒ᵣ Δ → X Δ' → Y Δ'

rename-⇒ₖ : ∀ {X Y} → Renameable (X ⇒ₖ Y)
rename-⇒ₖ ρ f _ ρ' = f _ (λ v → ρ' (ρ v))

-- Alternatively: □ A = I ⇒ₖ A
□ : (LinVarCtxt → Set) → (LinVarCtxt → Set)
□ A Δ = ∀ {Δ'} → (Δ' ⇒ᵣ Δ) → A Δ'

rename-□ : ∀ {A} → Renameable (□ A)
rename-□ ρ a ρ' = a (λ x → ρ' (ρ x))

------------------------------------------------------------------------------
-- Linear and Constraint Expressions in a normal form
data LinExp (Δ : LinVarCtxt) : Set where
  const : ℚ → LinExp Δ
  var   : ℚ → Var Δ → LinExp Δ --- FIXME: rename to _`*`var_
  _`+`_ : LinExp Δ → LinExp Δ → LinExp Δ

data ConstraintExp (Δ : LinVarCtxt) : Set where
  _`≤`_ : LinExp Δ → LinExp Δ → ConstraintExp Δ
  _`>`_ : LinExp Δ → LinExp Δ → ConstraintExp Δ
  _`=`_ : LinExp Δ → LinExp Δ → ConstraintExp Δ
  _`≠`_ : LinExp Δ → LinExp Δ → ConstraintExp Δ
  _`=`f_ : Var Δ → Var Δ → ConstraintExp Δ
  _`≠`f_ : Var Δ → Var Δ → ConstraintExp Δ
  _and_ : ConstraintExp Δ → ConstraintExp Δ → ConstraintExp Δ
  _or_  : ConstraintExp Δ → ConstraintExp Δ → ConstraintExp Δ

rename-LinExp : Renameable LinExp
rename-LinExp ρ (const q)   = const q
rename-LinExp ρ (var r x)   = var r (ρ x)
rename-LinExp ρ (e₁ `+` e₂) = (rename-LinExp ρ e₁) `+` (rename-LinExp ρ e₂)

rename-ConstraintExp : Renameable ConstraintExp
rename-ConstraintExp ρ (e₁ `≤` e₂) = rename-LinExp ρ e₁ `≤` rename-LinExp ρ e₂
rename-ConstraintExp ρ (e₁ `>` e₂) = rename-LinExp ρ e₁ `>` rename-LinExp ρ e₂
rename-ConstraintExp ρ (p and q)   = (rename-ConstraintExp ρ p) and (rename-ConstraintExp ρ q)
rename-ConstraintExp ρ (p or q)    = (rename-ConstraintExp ρ p) or (rename-ConstraintExp ρ q)
rename-ConstraintExp ρ (e₁ `=` e₂) = rename-LinExp ρ e₁ `=` rename-LinExp ρ e₂
rename-ConstraintExp ρ (e₁ `≠` e₂) = rename-LinExp ρ e₁ `≠` rename-LinExp ρ e₂
rename-ConstraintExp ρ (x₁ `=`f x₂) = ρ x₁ `=`f ρ x₂
rename-ConstraintExp ρ (x₁ `≠`f x₂) = ρ x₁ `≠`f ρ x₂

------------------------------------------------------------------------------
-- Operations

_⊛_ : ∀ {Δ} → ℚ → LinExp Δ → LinExp Δ
q ⊛ const x     = const (q ℚ.* x)
q ⊛ var r v     = var (q ℚ.* r) v
q ⊛ (e₁ `+` e₂) = (q ⊛ e₁) `+` (q ⊛ e₂)

negate : ∀ {Δ} → ConstraintExp Δ → ConstraintExp Δ
negate (e₁ `≤` e₂) = e₁ `>` e₂
negate (e₁ `>` e₂) = e₁ `≤` e₂
negate (p and q) = negate p or negate q
negate (p or q) = negate p and negate q
negate (e₁ `=` e₂) = e₁ `≠` e₂
negate (e₁ `≠` e₂) = e₁ `=` e₂
negate (x₁ `=`f x₂) = x₁ `≠`f x₂
negate (x₁ `≠`f x₂) = x₁ `=`f x₂

------------------------------------------------------------------------------
-- Evaluation

Env : LinVarCtxt → Set
Env Δ = Var Δ → ℚ

eval-LinExp : ∀ {Δ} → LinExp Δ → Env Δ → ℚ
eval-LinExp (const q)   η = q
eval-LinExp (var q x)   η = q * η x
eval-LinExp (e₁ `+` e₂) η = eval-LinExp e₁ η + eval-LinExp e₂ η

eval-⊛ : ∀ {Δ} q (e : LinExp Δ) η → q * eval-LinExp e η ≡ eval-LinExp (q ⊛ e) η
eval-⊛ q (const x) η = refl
eval-⊛ q (var r x) η = sym (*-assoc q r (η x))
eval-⊛ q (e₁ `+` e₂) η rewrite sym (eval-⊛ q e₁ η) rewrite sym (eval-⊛ q e₂ η) =
  *-distribˡ-+ q (eval-LinExp e₁ η) (eval-LinExp e₂ η)

-- FIXME: Make this a non-anonymous module so that we don't end up
-- parameterising every use with extFunc
module _ (extFunc : ℚ → ℚ) where

  eval-ConstraintExp : ∀ {Δ} → ConstraintExp Δ → Env Δ → Bool
  eval-ConstraintExp (e₁ `≤` e₂)  η = eval-LinExp e₁ η ≤ᵇ eval-LinExp e₂ η
  eval-ConstraintExp (e₁ `>` e₂)  η = not (eval-LinExp e₁ η ≤ᵇ eval-LinExp e₂ η)
  eval-ConstraintExp (e₁ `=` e₂)  η = (eval-LinExp e₁ η ≟ eval-LinExp e₂ η) .does
  eval-ConstraintExp (e₁ `≠` e₂)  η = not ((eval-LinExp e₁ η ≟ eval-LinExp e₂ η) .does)
  eval-ConstraintExp (p and q)    η = eval-ConstraintExp p η ∧ eval-ConstraintExp q η
  eval-ConstraintExp (p or q)     η = eval-ConstraintExp p η ∨ eval-ConstraintExp q η
  eval-ConstraintExp (x₁ `=`f x₂) η = (η x₁ ≟ extFunc (η x₂)) .does
  eval-ConstraintExp (x₁ `≠`f x₂) η = not ((η x₁ ≟ extFunc (η x₂)) .does)

  eval-negate : ∀ {Δ} (p : ConstraintExp Δ) η →
                not (eval-ConstraintExp p η) ≡ eval-ConstraintExp (negate p) η
  eval-negate (x `≤` x₁) η = refl
  eval-negate (x `>` x₁) η = not-involutive _
  eval-negate (x `=` x₁) η = refl
  eval-negate (x `≠` x₁) η = not-involutive _
  eval-negate (p and q)  η rewrite sym (eval-negate p η)
                           rewrite sym (eval-negate q η) =
                              deMorgan₁ (eval-ConstraintExp p η) (eval-ConstraintExp q η)
  eval-negate (p or q)   η rewrite sym (eval-negate p η)
                           rewrite sym (eval-negate q η) =
                              deMorgan₂ (eval-ConstraintExp p η) (eval-ConstraintExp q η)
  eval-negate (x₁ `=`f x₂) η = refl
  eval-negate (x₁ `≠`f x₂) η = not-involutive _

------------------------------------------------------------------------------
-- Part III: Existential Quantification monad
data Ex (A : LinVarCtxt → Set) : LinVarCtxt → Set where
  ex     : ∀ {Δ} → Ex A (Δ ,∙) → Ex A Δ
  if     : ∀ {Δ} → ConstraintExp Δ → Ex A Δ → Ex A Δ → Ex A Δ
  linexp : ∀ {Δ} → LinExp Δ → Ex A (Δ ,∙) → Ex A Δ
  funexp : ∀ {Δ} → {- fsymb → -} Var Δ → Ex A (Δ ,∙) → Ex A Δ
  return : ∀ {Δ} → A Δ → Ex A Δ

rename-Ex : ∀ {A} → Renameable A → Renameable (Ex A)
rename-Ex ren-A ρ (return a)   = return (ren-A ρ a)
rename-Ex ren-A ρ (ex e)       = ex (rename-Ex ren-A (under ρ) e)
rename-Ex ren-A ρ (if c tr fa) = if (rename-ConstraintExp ρ c) (rename-Ex ren-A ρ tr) (rename-Ex ren-A ρ fa)
rename-Ex ren-A ρ (linexp e k) = linexp (rename-LinExp ρ e) (rename-Ex ren-A (under ρ) k)
rename-Ex ren-A ρ (funexp x k) = funexp (ρ x) (rename-Ex ren-A (under ρ) k)

bind-ex : ∀ {Δ A B} → Ex A Δ → (A ⇒ₖ Ex B) Δ → Ex B Δ
bind-ex (return x)   f = f _ (λ x → x) x
bind-ex (if c tr fa) f = if c (bind-ex tr f) (bind-ex fa f)
bind-ex (ex x)       f = ex (bind-ex x (rename-⇒ₖ succ f))
bind-ex (linexp e k) f = linexp e (bind-ex k (rename-⇒ₖ succ f))
bind-ex (funexp x k) f = funexp x (bind-ex k (rename-⇒ₖ succ f))

------------------------------------------------------------------------
-- Part IV : Let/If lifting monad

-- FIXME: split this into a separate module because it is specific to
-- the Normalisation procedure

data LetLift (A : LinVarCtxt → Set) : LinVarCtxt → Set where
  return     : ∀ {Δ} → A Δ → LetLift A Δ
  if         : ∀ {Δ} → ConstraintExp Δ → LetLift A Δ → LetLift A Δ → LetLift A Δ
  let-linexp : ∀ {Δ} → LinExp Δ → LetLift A (Δ ,∙) → LetLift A Δ
  let-funexp : ∀ {Δ} → {- fsymb → -} Var Δ → LetLift A (Δ ,∙) → LetLift A Δ

-- FIXME: rename this
expand : ∀ {A Δ} → LetLift (Ex A) Δ → Ex A Δ
expand (return x)       = x
expand (if cond tr fa)  = if cond (expand tr) (expand fa)
expand (let-linexp e k) = linexp e (expand k)
expand (let-funexp x k) = funexp x (expand k)

rename-lift : ∀ {A} → Renameable A → Renameable (LetLift A)
rename-lift rA ρ (return x) =
  return (rA ρ x)
rename-lift rA ρ (if p k₁ k₂) =
  if (rename-ConstraintExp ρ p) (rename-lift rA ρ k₁) (rename-lift rA ρ k₂)
rename-lift rA ρ (let-linexp e k) =
  let-linexp (rename-LinExp ρ e) (rename-lift rA (under ρ) k)
rename-lift rA ρ (let-funexp v k) =
  let-funexp (ρ v) (rename-lift rA (under ρ) k)

bind-let : ∀ {Δ A B} → LetLift A Δ → (A ⇒ₖ LetLift B) Δ → LetLift B Δ
bind-let (return x)       f = f _ (λ x → x) x
bind-let (if e kt kf)     f = if e (bind-let kt f) (bind-let kf f)
bind-let (let-linexp e k) f = let-linexp e (bind-let k (rename-⇒ₖ succ f))
bind-let (let-funexp x k) f = let-funexp x (bind-let k (rename-⇒ₖ succ f))
