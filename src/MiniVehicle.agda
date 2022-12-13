{-# OPTIONS --postfix-projections --safe #-}

module MiniVehicle where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
-- open import Data.List.Relation.Unary.All using (All; map)
open import Data.Rational using (ℚ)

-- open import MiniVehicle.Qualifiers
-- open import KindTheory using (Signature)

data Kind (base : Set) : Set where
  Type : Kind base
  Base : base → Kind base

record Signature : Set₁ where
  field
    base      : Set
    op        : Set
    op-result : op → Kind base
    op-args   : op → List (Kind base)
    -- FIXME: equational theory???

module Syntax (S : Signature) where

  module S = Signature S

  data KindContext : Set where
    ε    : KindContext
    _,-_ : KindContext → S.base → KindContext

  data _⊢Tv_ : KindContext → S.base → Set where
    zero : ∀ {Δ κ} → (Δ ,- κ) ⊢Tv κ
    succ : ∀ {Δ κ κ'} → Δ ⊢Tv κ → (Δ ,- κ') ⊢Tv κ

  _⇒ᵣ_ : KindContext → KindContext → Set
  K₁ ⇒ᵣ K₂ = ∀ {κ} → K₂ ⊢Tv κ → K₁ ⊢Tv κ

  under : ∀ {K₁ K₂ κ} → (K₁ ⇒ᵣ K₂) → (K₁ ,- κ) ⇒ᵣ (K₂ ,- κ)
  under ρ zero     = zero
  under ρ (succ x) = succ (ρ x)

  wk : ∀ {K κ} → (K ,- κ) ⇒ᵣ K
  wk = succ

  mutual
    data _⊢T_ : KindContext → Kind S.base → Set where
      var    : ∀ {K κ} → K ⊢Tv κ → K ⊢T Base κ

      -- Built-in types
      _⇒_   : ∀ {K} → K ⊢T Type → K ⊢T Type → K ⊢T Type
      Forall : ∀ {K κ} → (K ,- κ) ⊢T Type → K ⊢T Type

      -- Constructors from the signature
      Op     : ∀ {K} → (op : S.op) → K ⊢T* S.op-args op → K ⊢T S.op-result op

    data _⊢T*_ : KindContext → List (Kind S.base) → Set where
      []  : ∀ {K} → K ⊢T* []
      _∷_ : ∀ {K κ κs} → K ⊢T κ → K ⊢T* κs → K ⊢T* (κ ∷ κs)

  mutual
    ren-Type : ∀ {K₁ K₂ κ} → (K₂ ⇒ᵣ K₁) → K₁ ⊢T κ → K₂ ⊢T κ
    ren-Type ρ (var x) = var (ρ x)
    ren-Type ρ (A ⇒ B) = (ren-Type ρ A) ⇒ (ren-Type ρ B)
    ren-Type ρ (Forall A) = Forall (ren-Type (under ρ) A)
    ren-Type ρ (Op op args) = Op op (ren-Types ρ args)

    ren-Types : ∀ {K₁ K₂ κs} → (K₂ ⇒ᵣ K₁) → K₁ ⊢T* κs → K₂ ⊢T* κs
    ren-Types ρ []       = []
    ren-Types ρ (A ∷ As) = ren-Type ρ A ∷ ren-Types ρ As

  _⇒ₛ_ : KindContext → KindContext → Set
  K₁ ⇒ₛ K₂ = ∀ {κ} → K₂ ⊢Tv κ → K₁ ⊢T Base κ

  binder : ∀ {K₁ K₂} → (K₂ ⇒ₛ K₁) → ∀ {κ} → (K₂ ,- κ) ⇒ₛ (K₁ ,- κ)
  binder σ zero     = var zero
  binder σ (succ x) = ren-Type wk (σ x)

  mutual
    subst-Type : ∀ {K₁ K₂} → (K₂ ⇒ₛ K₁) → ∀ {κ} → K₁ ⊢T κ → K₂ ⊢T κ
    subst-Type σ (var x) = σ x
    subst-Type σ (A ⇒ B) = subst-Type σ A ⇒ subst-Type σ B
    subst-Type σ (Forall A) = Forall (subst-Type (binder σ) A)
    subst-Type σ (Op op args) = Op op (subst-Types σ args)

    subst-Types : ∀ {K₁ K₂ κs} → (K₂ ⇒ₛ K₁) → K₁ ⊢T* κs → K₂ ⊢T* κs
    subst-Types ρ []       = []
    subst-Types ρ (A ∷ As) = subst-Type ρ A ∷ subst-Types ρ As

  single-sub : ∀ {K κ} → K ⊢T Base κ → K ⇒ₛ (K ,- κ)
  single-sub N zero = N
  single-sub N (succ x) = var x




  data Context : KindContext → Set where
    ε    : ∀ {Δ} → Context Δ
    _,-_ : ∀ {Δ} → Context Δ → Δ ⊢T Type → Context Δ

  infixl 10 _,-_

  ren-Context : ∀ {K₁ K₂} → (K₂ ⇒ᵣ K₁) → Context K₁ → Context K₂
  ren-Context ρ ε        = ε
  ren-Context ρ (Γ ,- A) = (ren-Context ρ Γ) ,- ren-Type ρ A

  data _⊢_∋_ : (Δ : KindContext) → Context Δ → Δ ⊢T Type → Set where
    zero : ∀ {Δ Γ A}   →             Δ ⊢ (Γ ,- A) ∋ A
    succ : ∀ {Δ Γ A B} → Δ ⊢ Γ ∋ A → Δ ⊢ (Γ ,- B) ∋ A

  data _/_⊢_ : (Δ : KindContext) → Context Δ → Δ ⊢T Type → Set where
    -- Variables
    var    : ∀ {Δ Γ A} → Δ ⊢ Γ ∋ A → Δ / Γ ⊢ A

    -- Functions
    ƛ      : ∀ {Δ Γ A B} →
             Δ / (Γ ,- A) ⊢ B →
             Δ / Γ ⊢ (A ⇒ B)
    _∙_    : ∀ {Δ Γ A B} →
             Δ / Γ ⊢ (A ⇒ B) →
             Δ / Γ ⊢ A →
             Δ / Γ ⊢ B

    -- Type quantification
    Λ      : ∀ {Δ Γ κ A} →
             (Δ ,- κ) / (ren-Context wk Γ) ⊢ A →
             Δ / Γ ⊢ Forall A
    _•_    : ∀ {Δ Γ κ A} →
             Δ / Γ ⊢ Forall A →
             (B : Δ ⊢T Base κ) →
             Δ / Γ ⊢ subst-Type (single-sub B) A
{-
    -- External functions
    func   : ∀ {Δ Γ} → Δ / Γ ⊢ Num (LinearityConst linear) → Δ / Γ ⊢ Num (LinearityConst linear)

    const  : ∀ {Δ Γ} → ℚ → Δ / Γ ⊢ Num (LinearityConst const)
    _`+_   : ∀ {Δ Γ l₁ l₂ l₃} → Δ / Γ ⊢ MaxLin l₁ l₂ l₃ → Δ / Γ ⊢ Num l₁ → Δ / Γ ⊢ Num l₂ → Δ / Γ ⊢ Num l₃
    _`*_   : ∀ {Δ Γ l₁ l₂ l₃} → Δ / Γ ⊢ HasMul l₁ l₂ l₃ → Δ / Γ ⊢ Num l₁ → Δ / Γ ⊢ Num l₂ → Δ / Γ ⊢ Num l₃

    -- Vecs
    foreach : ∀ {Δ Γ} → (n : Δ ⊢T Nat) (A : Δ ⊢T Type) → Δ / (Γ ,- Index n) ⊢ A → Δ / Γ ⊢ Vec n A
    index   : ∀ {Δ Γ} → (n : Δ ⊢T Nat) (A : Δ ⊢T Type) → Δ / Γ ⊢ Vec n A → Δ / Γ ⊢ Index n → Δ / Γ ⊢ A
    idx     : ∀ {Δ Γ n} → (i : Fin n) → Δ / Γ ⊢ Index [ n ]
    -- FIXME: crush/fold/reduce

    -- Comparisons
    _`≤_   : ∀ {Δ Γ l₁ l₂ l₃} → Δ / Γ ⊢ MaxLin l₁ l₂ l₃ → Δ / Γ ⊢ Num l₁ → Δ / Γ ⊢ Num l₂ → Δ / Γ ⊢ Bool l₃ (PolarityConst U)

    -- Polymorphic if-then-else
    if_then_else_ : ∀ {Δ Γ A}
       (cond : Δ / Γ ⊢ Bool (LinearityConst linear) (PolarityConst U))
       (on-true on-false : Δ / Γ ⊢ A) →
       Δ / Γ ⊢ A
    -- FIXME: need an 'almost equal' typeclass constraint here; can make it as complex as needed
    -- Soundness counterexample: forall (x : Rat) . f 10 ! (if (x >= 7) then 0 else 1) == 0

    -- Logic
    _`∧_ _`∨_ : ∀ {Δ Γ l₁ l₂ l₃ p₁ p₂ p₃} →
              Δ / Γ ⊢ MaxLin l₁ l₂ l₃ →
              Δ / Γ ⊢ MaxPol p₁ p₂ p₃ →
              Δ / Γ ⊢ Bool l₁ p₁ →
              Δ / Γ ⊢ Bool l₂ p₂ →
              Δ / Γ ⊢ Bool l₃ p₃
    `¬_ : ∀ {Δ Γ l p₁ p₂} →
          Δ / Γ ⊢ NegPol p₁ p₂ →
          Δ / Γ ⊢ Bool l p₁ →
          Δ / Γ ⊢ Bool l p₂
    ∃   : ∀ {Δ Γ p₁ p₂ l} →
          Δ / Γ ⊢ Quantify p₁ p₂ →
          Δ / Γ ⊢ (Num (LinearityConst linear) ⇒ Bool l p₁) →
          Δ / Γ ⊢ Bool l p₂

    -- Evidence for usage of the operations
    maxlin : ∀ {Δ Γ l₁ l₂ l₃} →
             MaxLinRel l₁ l₂ l₃ →
             Δ / Γ ⊢ MaxLin (LinearityConst l₁) (LinearityConst l₂) (LinearityConst l₃)
    hasmul : ∀ {Δ Γ l₁ l₂ l₃} →
             MulRel l₁ l₂ l₃ →
             Δ / Γ ⊢ HasMul (LinearityConst l₁) (LinearityConst l₂) (LinearityConst l₃)
    maxpol : ∀ {Δ Γ p₁ p₂ p₃} →
             MaxPolRel p₁ p₂ p₃ →
             Δ / Γ ⊢ MaxPol (PolarityConst p₁) (PolarityConst p₂) (PolarityConst p₃)
    negpol : ∀ {Δ Γ p₁ p₂} →
             NegPolRel p₁ p₂ →
             Δ / Γ ⊢ NegPol (PolarityConst p₁) (PolarityConst p₂)
    quantify : ∀ {Δ Γ p₁ p₂} →
               QuantifyRel p₁ p₂ →
               Δ / Γ ⊢ Quantify (PolarityConst p₁) (PolarityConst p₂)
-}
