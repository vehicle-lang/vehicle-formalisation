{-# OPTIONS --postfix-projections --safe #-}

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Rational using (ℚ)

open import MiniVehicle.Language.Syntax.Kind
open import MiniVehicle.Language.Syntax.Restriction

module MiniVehicle.Language.Syntax.Type (R : Restriction) where

open Restriction R

-- Type variables

infix 1 _⊢Tv_

data _⊢Tv_ : KindContext → Kind → Set where
  zero : Δ ,- κ ⊢Tv κ
  succ : Δ ⊢Tv κ
       → Δ ,- κ′ ⊢Tv κ


-- Types

infix 1 _⊢T_

data _⊢T_ : KindContext → Kind → Set where
  var          : Δ ⊢Tv κ → Δ ⊢T κ
  _⇒_          : Δ ⊢T Type → Δ ⊢T Type → Δ ⊢T Type
  Forall       : is-small κ → Δ ,- κ ⊢T Type → Δ ⊢T Type

  Bool         : Δ ⊢T BoolRes → Δ ⊢T Type
  Num          : Δ ⊢T NumRes → Δ ⊢T Type

  Index        : Δ ⊢T Nat → Δ ⊢T Type
  Vec          : Δ ⊢T Nat → Δ ⊢T Type → Δ ⊢T Type
  [_]          : ℕ → Δ ⊢T Nat

  NumRes       : NumRestriction → Δ ⊢T NumRes
  NumConstRes  : Δ ⊢T NumRes → Δ ⊢T Type
  FuncRes      : Δ ⊢T NumRes → Δ ⊢T NumRes → Δ ⊢T Type
  AddRes       : Δ ⊢T NumRes → Δ ⊢T NumRes → Δ ⊢T NumRes → Δ ⊢T Type
  MulRes       : Δ ⊢T NumRes → Δ ⊢T NumRes → Δ ⊢T NumRes → Δ ⊢T Type

  BoolRes      : BoolRestriction → Δ ⊢T BoolRes
  BoolConstRes : Δ ⊢T BoolRes → Δ ⊢T Type
  NotRes       : Δ ⊢T BoolRes → Δ ⊢T BoolRes → Δ ⊢T Type
  AndRes       : Δ ⊢T BoolRes → Δ ⊢T BoolRes → Δ ⊢T BoolRes → Δ ⊢T Type
  OrRes        : Δ ⊢T BoolRes → Δ ⊢T BoolRes → Δ ⊢T BoolRes → Δ ⊢T Type
  CompRes      : Δ ⊢T NumRes → Δ ⊢T NumRes → Δ ⊢T BoolRes → Δ ⊢T Type
  QuantRes     : Δ ⊢T NumRes → Δ ⊢T BoolRes → Δ ⊢T BoolRes → Δ ⊢T Type
  IfRes        : Δ ⊢T BoolRes → Δ ⊢T Type


-- Type contexts

data Context : KindContext → Set where
  ε    : Context Δ
  _,-_ : Context Δ → Δ ⊢T Type → Context Δ

infixl 10 _,-_

variable
  Γ  : Context Δ
  Γ′ : Context Δ′


-- Type variable renamings

infix 1 _⇒ᵣ_

_⇒ᵣ_ : KindContext → KindContext → Set
Δ ⇒ᵣ Δ′ = ∀ {κ} → Δ′ ⊢Tv κ → Δ ⊢Tv κ

under : Δ ⇒ᵣ Δ′ → Δ ,- κ ⇒ᵣ Δ′ ,- κ
under ρ zero     = zero
under ρ (succ x) = succ (ρ x)

wk : Δ ,- κ ⇒ᵣ Δ
wk = succ

ren-Type : Δ′ ⇒ᵣ Δ → Δ ⊢T κ → Δ′ ⊢T κ
ren-Type ρ (var x) = var (ρ x)
ren-Type ρ (Bool r) = Bool (ren-Type ρ r)
ren-Type ρ (Num r) = Num (ren-Type ρ r)
ren-Type ρ (A ⇒ B) = (ren-Type ρ A) ⇒ (ren-Type ρ B)
ren-Type ρ (Index A) = Index (ren-Type ρ A)
ren-Type ρ (Vec A B) = Vec (ren-Type ρ A) (ren-Type ρ B)
ren-Type ρ (Forall s A) = Forall s (ren-Type (under ρ) A)
ren-Type ρ [ n ] = [ n ]
-- Number restrictions
ren-Type ρ (NumRes l) = NumRes l
ren-Type ρ (NumConstRes l) = NumConstRes (ren-Type ρ l)
ren-Type ρ (FuncRes l₁ l₂) = FuncRes (ren-Type ρ l₁) (ren-Type ρ l₂)
ren-Type ρ (AddRes l₁ l₂ l₃) = AddRes (ren-Type ρ l₁) (ren-Type ρ l₂) (ren-Type ρ l₃)
ren-Type ρ (MulRes l₁ l₂ l₃) = MulRes (ren-Type ρ l₁) (ren-Type ρ l₂) (ren-Type ρ l₃)
-- Bool restrictions
ren-Type ρ (BoolRes p) = BoolRes p
ren-Type ρ (BoolConstRes p) = BoolConstRes (ren-Type ρ p)
ren-Type ρ (AndRes p₁ p₂ p₃) = AndRes (ren-Type ρ p₁) (ren-Type ρ p₂) (ren-Type ρ p₃)
ren-Type ρ (OrRes p₁ p₂ p₃) = OrRes (ren-Type ρ p₁) (ren-Type ρ p₂) (ren-Type ρ p₃)
ren-Type ρ (CompRes p₁ p₂ p₃) = CompRes (ren-Type ρ p₁) (ren-Type ρ p₂) (ren-Type ρ p₃)
ren-Type ρ (NotRes p₁ p₂)  = NotRes (ren-Type ρ p₁) (ren-Type ρ p₂)
ren-Type ρ (QuantRes l p₁ p₂)  = QuantRes (ren-Type ρ l) (ren-Type ρ p₁) (ren-Type ρ p₂)
ren-Type ρ (IfRes p)  = IfRes (ren-Type ρ p)

ren-Context : ∀ {Δ Δ′} → (Δ′ ⇒ᵣ Δ) → Context Δ → Context Δ′
ren-Context ρ ε        = ε
ren-Context ρ (Γ ,- A) = (ren-Context ρ Γ) ,- ren-Type ρ A


-- Type variable substitutions

infix 1 _⇒ₛ_

_⇒ₛ_ : KindContext → KindContext → Set
Δ ⇒ₛ Δ′ = ∀ {κ} → Δ′ ⊢Tv κ → Δ ⊢T κ

binder : Δ′ ⇒ₛ Δ → ∀ {κ} → Δ′ ,- κ ⇒ₛ Δ ,- κ
binder σ zero     = var zero
binder σ (succ x) = ren-Type wk (σ x)

subst-Type : Δ′ ⇒ₛ Δ → ∀ {κ} → Δ ⊢T κ → Δ′ ⊢T κ
subst-Type σ (var x) = σ x
subst-Type σ (Bool r) = Bool (subst-Type σ r)
subst-Type σ (Num r) = Num (subst-Type σ r)
subst-Type σ (A ⇒ B) = (subst-Type σ A) ⇒ (subst-Type σ B)
subst-Type σ (Index A) = Index (subst-Type σ A)
subst-Type σ (Vec A B) = Vec (subst-Type σ A) (subst-Type σ B)
subst-Type σ (Forall s A) = Forall s (subst-Type (binder σ) A)
subst-Type σ [ n ] = [ n ]
-- Number restrictions
subst-Type σ (NumRes l) = NumRes l
subst-Type σ (NumConstRes l) = NumConstRes (subst-Type σ l)
subst-Type σ (FuncRes l₁ l₂) = FuncRes (subst-Type σ l₁) (subst-Type σ l₂)
subst-Type σ (AddRes l₁ l₂ l₃) = AddRes (subst-Type σ l₁) (subst-Type σ l₂) (subst-Type σ l₃)
subst-Type σ (MulRes l₁ l₂ l₃) = MulRes (subst-Type σ l₁) (subst-Type σ l₂) (subst-Type σ l₃)
-- Bool restrictions
subst-Type σ (BoolRes p) = BoolRes p
subst-Type σ (BoolConstRes p) = BoolConstRes (subst-Type σ p)
subst-Type σ (AndRes p₁ p₂ p₃) = AndRes (subst-Type σ p₁) (subst-Type σ p₂) (subst-Type σ p₃)
subst-Type σ (OrRes p₁ p₂ p₃) = OrRes (subst-Type σ p₁) (subst-Type σ p₂) (subst-Type σ p₃)
subst-Type σ (CompRes p₁ p₂ p₃) = CompRes (subst-Type σ p₁) (subst-Type σ p₂) (subst-Type σ p₃)
subst-Type σ (NotRes p₁ p₂)  = NotRes (subst-Type σ p₁) (subst-Type σ p₂)
subst-Type σ (QuantRes l p₁ p₂)  = QuantRes (subst-Type σ l) (subst-Type σ p₁) (subst-Type σ p₂)
subst-Type σ (IfRes p)  = IfRes (subst-Type σ p)

single-sub : ∀ {K κ} → K ⊢T κ → K ⇒ₛ (K ,- κ)
single-sub N zero = N
single-sub N (succ x) = var x
