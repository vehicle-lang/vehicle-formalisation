{-# OPTIONS --postfix-projections --safe #-}

open import MiniVehicle.Language.Syntax.Restriction

module MiniVehicle.Language.Syntax.Term (R : Restriction) where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Rational using (ℚ)
open import MiniVehicle.Language.Syntax.Kind
open import MiniVehicle.Language.Syntax.Type R

open Restriction R

data _⊢_∋_ : (Δ : KindContext) → Context Δ → Δ ⊢T Type → Set where
  zero : ∀ {A}   →             Δ ⊢ (Γ ,- A) ∋ A
  succ : ∀ {A B} → Δ ⊢ Γ ∋ A → Δ ⊢ (Γ ,- B) ∋ A

data _/_⊢_ : (Δ : KindContext) → Context Δ → Δ ⊢T Type → Set where
  -- Variables
  var    : ∀ {A} → Δ ⊢ Γ ∋ A → Δ / Γ ⊢ A

  -- Functions
  ƛ      : ∀ {A B} →
           Δ / (Γ ,- A) ⊢ B →
           Δ / Γ ⊢ (A ⇒ B)
  _∙_    : ∀ {A B} →
           Δ / Γ ⊢ (A ⇒ B) →
           Δ / Γ ⊢ A →
           Δ / Γ ⊢ B

  -- Type quantification
  Λ      : ∀ {κ A} →
           (s : is-small κ) →
           (Δ ,- κ) / (ren-Context wk Γ) ⊢ A →
           Δ / Γ ⊢ Forall s A
  _•_    : ∀ {κ s A} →
           Δ / Γ ⊢ Forall s A →
           (B : Δ ⊢T κ) →
           Δ / Γ ⊢ subst-Type (single-sub B) A

  -- External functions
  func   : ∀ {r₁ r₂} → Δ / Γ ⊢ FuncRes r₁ r₂ → Δ / Γ ⊢ Num r₁ → Δ / Γ ⊢ Num r₂

  const  : ∀ {r₁} → Δ / Γ ⊢ NumConstRes r₁ → ℚ → Δ / Γ ⊢ Num r₁
  _`+_   : ∀ {l₁ l₂ l₃} → Δ / Γ ⊢ AddRes l₁ l₂ l₃ → Δ / Γ ⊢ Num l₁ → Δ / Γ ⊢ Num l₂ → Δ / Γ ⊢ Num l₃
  _`*_   : ∀ {l₁ l₂ l₃} → Δ / Γ ⊢ MulRes l₁ l₂ l₃ → Δ / Γ ⊢ Num l₁ → Δ / Γ ⊢ Num l₂ → Δ / Γ ⊢ Num l₃

  -- Vecs
  foreach : (n : Δ ⊢T Nat) (A : Δ ⊢T Type) → Δ / (Γ ,- Index n) ⊢ A → Δ / Γ ⊢ Vec n A
  index   : (n : Δ ⊢T Nat) (A : Δ ⊢T Type) → Δ / Γ ⊢ Vec n A → Δ / Γ ⊢ Index n → Δ / Γ ⊢ A
  idx     : ∀ {n} → (i : Fin n) → Δ / Γ ⊢ Index [ n ]
  -- FIXME: crush/fold/reduce

  -- Comparisons
  _`≤_   : ∀ {l₁ l₂ l₃} → Δ / Γ ⊢ CompRes l₁ l₂ l₃ → Δ / Γ ⊢ Num l₁ → Δ / Γ ⊢ Num l₂ → Δ / Γ ⊢ Bool l₃
  _`<_   : ∀ {l₁ l₂ l₃} → Δ / Γ ⊢ CompRes l₁ l₂ l₃ → Δ / Γ ⊢ Num l₁ → Δ / Γ ⊢ Num l₂ → Δ / Γ ⊢ Bool l₃

  -- Polymorphic if-then-else
  if_then_else_ : ∀ {A r₁} → Δ / Γ ⊢ IfRes r₁ →
     (cond : Δ / Γ ⊢ Bool r₁)
     (on-true on-false : Δ / Γ ⊢ A) →
     Δ / Γ ⊢ A
  -- FIXME: need an 'almost equal' typeclass constraint here; can make it as complex as needed
  -- Soundness counterexample: forall (x : Rat) . f 10 ! (if (x >= 7) then 0 else 1) == 0

  -- Logic
  _`∧_ : ∀ {r₁ r₂ r₃} → Δ / Γ ⊢ AndRes r₁ r₂ r₃ → Δ / Γ ⊢ Bool r₁ → Δ / Γ ⊢ Bool r₂ → Δ / Γ ⊢ Bool r₃
  _`∨_ : ∀ {b₁ b₂ b₃} → Δ / Γ ⊢ OrRes b₁ b₂ b₃ → Δ / Γ ⊢ Bool b₁ → Δ / Γ ⊢ Bool b₂ → Δ / Γ ⊢ Bool b₃
  `¬_ : ∀ {b₁ b₂} → Δ / Γ ⊢ NotRes b₁ b₂ → Δ / Γ ⊢ Bool b₁ → Δ / Γ ⊢ Bool b₂
  ∃   : ∀ {n₁ b₁ b₂} →
        Δ / Γ ⊢ QuantRes n₁ b₁ b₂ →
        Δ / Γ ⊢ (Num n₁ ⇒ Bool b₁) →
        Δ / Γ ⊢ Bool b₂

  -- Evidence for usage of the operations
  numConstRes : ∀ {l} → NumConstRestriction l → Δ / Γ ⊢ NumConstRes (NumRes l)
  funcRes : ∀ {l₁ l₂} → FuncRestriction l₁ l₂ → Δ / Γ ⊢ FuncRes (NumRes l₁) (NumRes l₂)
  addRes : ∀ {l₁ l₂ l₃} →
           AddRestriction l₁ l₂ l₃ →
           Δ / Γ ⊢ AddRes (NumRes l₁) (NumRes l₂) (NumRes l₃)
  mulRes : ∀ {l₁ l₂ l₃} →
           MulRestriction l₁ l₂ l₃ →
           Δ / Γ ⊢ MulRes (NumRes l₁) (NumRes l₂) (NumRes l₃)

  boolConstRes : ∀ {b} → BoolConstRestriction b → Δ / Γ ⊢ BoolConstRes (BoolRes b)
  notRes : ∀ {p₁ p₂} → NotRestriction p₁ p₂ →
           Δ / Γ ⊢ NotRes (BoolRes p₁) (BoolRes p₂)
  andRes : ∀ {p₁ p₂ p₃} → AndRestriction p₁ p₂ p₃ →
           Δ / Γ ⊢ AndRes (BoolRes p₁) (BoolRes p₂) (BoolRes p₃)
  orRes  : ∀ {p₁ p₂ p₃} → OrRestriction p₁ p₂ p₃ →
           Δ / Γ ⊢ OrRes (BoolRes p₁) (BoolRes p₂) (BoolRes p₃)
  compRes : ∀ {n₁ n₂ b} → CompRestriction n₁ n₂ b →
           Δ / Γ ⊢ CompRes (NumRes n₁) (NumRes n₂) (BoolRes b)
  quantRes : ∀ {n p₁ p₂} → QuantRestriction n p₁ p₂ →
             Δ / Γ ⊢ QuantRes (NumRes n) (BoolRes p₁) (BoolRes p₂)
  ifRes : ∀ {b} → IfRestriction b →
          Δ / Γ ⊢ IfRes (BoolRes b)
