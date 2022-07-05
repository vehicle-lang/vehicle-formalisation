module norm-expr where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; if_then_else_; not)
open import Data.Bool.Properties using (not-involutive)
open import Algebra.Properties.BooleanAlgebra (Data.Bool.Properties.∨-∧-booleanAlgebra) using (deMorgan₁; deMorgan₂)
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

Renameable : (LinVarCtxt → Set) → Set
Renameable A = ∀ {Δ Δ'} → (Δ ⇒ᵣ Δ') → A Δ' → A Δ

K : Set → LinVarCtxt → Set
K A Δ = A

rename-K : ∀ {A} → Renameable (K A)
rename-K _ a = a

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
  var   : ℚ → Var Δ → LinExp Δ
  _`+_  : LinExp Δ → LinExp Δ → LinExp Δ

data ConstraintExp (Δ : LinVarCtxt) : Set where
  _`≤`_ : LinExp Δ → LinExp Δ → ConstraintExp Δ
  _`>`_ : LinExp Δ → LinExp Δ → ConstraintExp Δ
  _`=`_ : LinExp Δ → LinExp Δ → ConstraintExp Δ
  _`≠`_ : LinExp Δ → LinExp Δ → ConstraintExp Δ
  _and_ : ConstraintExp Δ → ConstraintExp Δ → ConstraintExp Δ
  _or_  : ConstraintExp Δ → ConstraintExp Δ → ConstraintExp Δ
-- FIXME: add function (dis)equations

rename-LinExp : Renameable LinExp
rename-LinExp ρ (const q)  = const q
rename-LinExp ρ (var r x)  = var r (ρ x)
rename-LinExp ρ (e₁ `+ e₂) = (rename-LinExp ρ e₁) `+ (rename-LinExp ρ e₂)

rename-ConstraintExp : Renameable ConstraintExp
rename-ConstraintExp ρ (e₁ `≤` e₂) = rename-LinExp ρ e₁ `≤` rename-LinExp ρ e₂
rename-ConstraintExp ρ (e₁ `>` e₂) = rename-LinExp ρ e₁ `>` rename-LinExp ρ e₂
rename-ConstraintExp ρ (p and q)   = (rename-ConstraintExp ρ p) and (rename-ConstraintExp ρ q)
rename-ConstraintExp ρ (p or q)    = (rename-ConstraintExp ρ p) or (rename-ConstraintExp ρ q)
rename-ConstraintExp ρ (e₁ `=` e₂) = rename-LinExp ρ e₁ `=` rename-LinExp ρ e₂
rename-ConstraintExp ρ (e₁ `≠` e₂) = rename-LinExp ρ e₁ `≠` rename-LinExp ρ e₂

------------------------------------------------------------------------------
-- Operations

_⊛_ : ∀ {Δ} → ℚ → LinExp Δ → LinExp Δ
q ⊛ const x    = const (q ℚ.* x)
q ⊛ var r v    = var (q ℚ.* r) v
q ⊛ (e₁ `+ e₂) = (q ⊛ e₁) `+ (q ⊛ e₂)

negate : ∀ {Δ} → ConstraintExp Δ → ConstraintExp Δ
negate (e₁ `≤` e₂) = e₁ `>` e₂
negate (e₁ `>` e₂) = e₁ `≤` e₂
negate (p and q) = negate p or negate q
negate (p or q) = negate p and negate q
negate (e₁ `=` e₂) = e₁ `≠` e₂
negate (e₁ `≠` e₂) = e₁ `=` e₂

------------------------------------------------------------------------------
-- Evaluation

Env : LinVarCtxt → Set
Env Δ = Var Δ → ℚ

eval-LinExp : ∀ {Δ} → LinExp Δ → Env Δ → ℚ
eval-LinExp (const q)  η = q
eval-LinExp (var q x)  η = q * η x
eval-LinExp (e₁ `+ e₂) η = eval-LinExp e₁ η + eval-LinExp e₂ η

eval-⊛ : ∀ {Δ} q (e : LinExp Δ) η → q * eval-LinExp e η ≡ eval-LinExp (q ⊛ e) η
eval-⊛ q (const x) η = refl
eval-⊛ q (var r x) η = sym (*-assoc q r (η x))
eval-⊛ q (e₁ `+ e₂) η rewrite sym (eval-⊛ q e₁ η) rewrite sym (eval-⊛ q e₂ η) =
  *-distribˡ-+ q (eval-LinExp e₁ η) (eval-LinExp e₂ η)

eval-ConstraintExp : ∀ {Δ} → ConstraintExp Δ → Env Δ → Bool
eval-ConstraintExp (e₁ `≤` e₂) η = eval-LinExp e₁ η ≤ᵇ eval-LinExp e₂ η
eval-ConstraintExp (e₁ `>` e₂) η = not (eval-LinExp e₁ η ≤ᵇ eval-LinExp e₂ η)
eval-ConstraintExp (e₁ `=` e₂) η = (eval-LinExp e₁ η ≟ eval-LinExp e₂ η) .does
eval-ConstraintExp (e₁ `≠` e₂) η = not ((eval-LinExp e₁ η ≟ eval-LinExp e₂ η) .does)
eval-ConstraintExp (p and q)   η = eval-ConstraintExp p η ∧ eval-ConstraintExp q η
eval-ConstraintExp (p or q)    η = eval-ConstraintExp p η ∨ eval-ConstraintExp q η

eval-negate : ∀ {Δ} (p : ConstraintExp Δ) η → not (eval-ConstraintExp p η) ≡ eval-ConstraintExp (negate p) η
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

------------------------------------------------------------------------------
-- Part III : Let/If lifting monad

-- NOTE: the □ is needed on the second argument of 'if' to satisfy the
-- termination checker in the definition of expand.
data LetLift (A : LinVarCtxt → Set) : LinVarCtxt → Set where
  return  : ∀ {Δ} → A Δ → LetLift A Δ
  if      : ∀ {Δ} → ConstraintExp Δ → LetLift A Δ → □ (LetLift A) Δ → LetLift A Δ
  let-exp : ∀ {Δ} → LinExp Δ → LetLift A (Δ ,∙) → LetLift A Δ

-- Interprets 'if' as an actual if-then-else, and 'let' as extending
-- the environment by the value of an expression.
eval-Let : ∀ {X : Set}{A} →
           (∀ {Δ} → A Δ → Env Δ → X) →
           ∀ {Δ} → LetLift A Δ → Env Δ → X
eval-Let evalA (return x)    η = evalA x η
eval-Let evalA (if p k₁ k₂)  η =
  if (eval-ConstraintExp p η)
  then (eval-Let evalA k₁ η)
  else (eval-Let evalA (k₂ (λ v → v)) η)
eval-Let evalA (let-exp e k) η =
  eval-Let evalA k (λ { zero → eval-LinExp e η ; (succ x) → η x })

rename-lift : ∀ {A} → Renameable A → Renameable (LetLift A)
rename-lift rA ρ (return x) =
  return (rA ρ x)
rename-lift rA ρ (if p k₁ k₂) =
  if (rename-ConstraintExp ρ p) (rename-lift rA ρ k₁) (rename-□ ρ k₂)
rename-lift rA ρ (let-exp e k) =
  let-exp (rename-LinExp ρ e) (rename-lift rA (under ρ) k)

`if : ∀ {Δ} → ConstraintExp Δ → LetLift (λ _ → Bool) Δ
`if e = if e (return true) (λ ρ → return false)

`let : ∀ {Δ} → LinExp Δ → LetLift LinExp Δ
`let e = let-exp e (return (var 1ℚ zero))

bind-let : ∀ {Δ A B} → LetLift A Δ → (A ⇒ₖ LetLift B) Δ → LetLift B Δ
bind-let (return x)    f = f _ (λ x → x) x
bind-let (if e kt kf)  f = if e (bind-let kt f) λ ρ → bind-let (kf ρ) (rename-⇒ₖ ρ f)
bind-let (let-exp x k) f = let-exp x (bind-let k (rename-⇒ₖ succ f))

------------------------------------------------------------------------------
-- Existential Quantification monad

data Ex (A : LinVarCtxt → Set) : LinVarCtxt → Set where
  ex      : ∀ {Δ} → Ex A (Δ ,∙) → Ex A Δ
  return  : ∀ {Δ} → A Δ → Ex A Δ

bind-ex : ∀ {Δ A B} → Ex A Δ → (A ⇒ₖ Ex B) Δ → Ex B Δ
bind-ex (ex x) f = ex (bind-ex x (rename-⇒ₖ succ f))
bind-ex (return x) f = f _ (λ x → x) x

expand : ∀ {Δ} → LetLift (Ex ConstraintExp) Δ → Ex ConstraintExp Δ
expand (return x) = x
expand (if e kt kf) =
  bind-ex (expand kt) λ Δ' ρ xt →
  bind-ex (expand (kf ρ)) λ Δ'' ρ' xf →
  let e = rename-ConstraintExp (λ v → ρ' (ρ v)) e in
  return ((negate e and rename-ConstraintExp ρ' xt)
          or
          (e and xf))
expand (let-exp x p) =
  ex (bind-ex (expand p) λ Δ' ρ p' →
      return (((var 1ℚ (ρ zero)) `=` rename-LinExp (λ v → ρ (succ v)) x) and p'))
