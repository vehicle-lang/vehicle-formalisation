{-# OPTIONS --postfix-projections --safe #-}

module MiniVehicle where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Rational using (ℚ)

{-
data Linearity : Set where
  const linear : Linearity

data BoolKind : Set where
  constraint query : BoolKind
-}

data Kind : Set where
  Nat Type Linearity Polarity : Kind

data SmallKind : Kind → Set where
  Nat       : SmallKind Nat
  Linearity : SmallKind Linearity
  Polarity  : SmallKind Polarity

data KindContext : Set where
  ε    : KindContext
  _,-_ : KindContext → Kind → KindContext

data _⊢Tv_ : KindContext → Kind → Set where
  zero : ∀ {Δ κ} → (Δ ,- κ) ⊢Tv κ
  succ : ∀ {Δ κ κ'} → Δ ⊢Tv κ → (Δ ,- κ') ⊢Tv κ

_⇒ᵣ_ : KindContext → KindContext → Set
K₁ ⇒ᵣ K₂ = ∀ {κ} → K₂ ⊢Tv κ → K₁ ⊢Tv κ

under : ∀ {K₁ K₂ κ} → (K₁ ⇒ᵣ K₂) → (K₁ ,- κ) ⇒ᵣ (K₂ ,- κ)
under ρ zero     = zero
under ρ (succ x) = succ (ρ x)

wk : ∀ {K κ} → (K ,- κ) ⇒ᵣ K
wk = succ

data _⊢T_ : KindContext → Kind → Set where
  var    : ∀ {Δ κ} → Δ ⊢Tv κ → Δ ⊢T κ
  Bool   : ∀ {Δ} → Δ ⊢T Linearity → Δ ⊢T Polarity → Δ ⊢T Type
  Num    : ∀ {Δ} → Δ ⊢T Linearity → Δ ⊢T Type
  _⇒_   : ∀ {Δ} → Δ ⊢T Type → Δ ⊢T Type → Δ ⊢T Type
  Index  : ∀ {Δ} → Δ ⊢T Nat → Δ ⊢T Type
  Array  : ∀ {Δ} → Δ ⊢T Nat → Δ ⊢T Type → Δ ⊢T Type
  Forall : ∀ {Δ κ} → SmallKind κ → (Δ ,- κ) ⊢T Type → Δ ⊢T Type
  [_]    : ∀ {Δ} → ℕ → Δ ⊢T Nat
--
  const linear : ∀ {Δ} → Δ ⊢T Linearity
  U Ex   : ∀ {Δ} → Δ ⊢T Polarity
  MaxLin : ∀ {Δ} → Δ ⊢T Linearity → Δ ⊢T Linearity → Δ ⊢T Linearity → Δ ⊢T Type
  HasMul : ∀ {Δ} → Δ ⊢T Linearity → Δ ⊢T Linearity → Δ ⊢T Linearity → Δ ⊢T Type
  MaxPol : ∀ {Δ} → Δ ⊢T Polarity → Δ ⊢T Polarity → Δ ⊢T Polarity → Δ ⊢T Type
  NegPol : ∀ {Δ} → Δ ⊢T Polarity → Δ ⊢T Polarity → Δ ⊢T Type
  Quantify : ∀ {Δ} → Δ ⊢T Polarity → Δ ⊢T Polarity → Δ ⊢T Type

-- evidence rules:
-- one each for the things in

ren-Type : ∀ {K₁ K₂ κ} → (K₂ ⇒ᵣ K₁) → K₁ ⊢T κ → K₂ ⊢T κ
ren-Type ρ (var x) = var (ρ x)
ren-Type ρ (Bool l x) = Bool (ren-Type ρ l) (ren-Type ρ x)
ren-Type ρ (Num x) = Num (ren-Type ρ x)
ren-Type ρ (A ⇒ B) = (ren-Type ρ A) ⇒ (ren-Type ρ B)
ren-Type ρ (Index A) = Index (ren-Type ρ A)
ren-Type ρ (Array A B) = Array (ren-Type ρ A) (ren-Type ρ B)
ren-Type ρ (Forall s A) = Forall s (ren-Type (under ρ) A)
ren-Type ρ [ n ] = [ n ]
ren-Type ρ const = const
ren-Type ρ linear = linear
ren-Type ρ U = U
ren-Type ρ Ex = Ex
ren-Type ρ (MaxLin l₁ l₂ l₃) = MaxLin (ren-Type ρ l₁) (ren-Type ρ l₂) (ren-Type ρ l₃)
ren-Type ρ (MaxPol p₁ p₂ p₃) = MaxPol (ren-Type ρ p₁) (ren-Type ρ p₂) (ren-Type ρ p₃)
ren-Type ρ (HasMul l₁ l₂ l₃) = HasMul (ren-Type ρ l₁) (ren-Type ρ l₂) (ren-Type ρ l₃)
ren-Type ρ (NegPol p₁ p₂)  = NegPol (ren-Type ρ p₁) (ren-Type ρ p₂)
ren-Type ρ (Quantify p₁ p₂)  = Quantify (ren-Type ρ p₁) (ren-Type ρ p₂)

_⇒ₛ_ : KindContext → KindContext → Set
K₁ ⇒ₛ K₂ = ∀ {κ} → K₂ ⊢Tv κ → K₁ ⊢T κ

binder : ∀ {K₁ K₂} → (K₂ ⇒ₛ K₁) → ∀ {κ} → (K₂ ,- κ) ⇒ₛ (K₁ ,- κ)
binder σ zero     = var zero
binder σ (succ x) = ren-Type wk (σ x)

subst-Type : ∀ {K₁ K₂} → (K₂ ⇒ₛ K₁) → ∀ {κ} → K₁ ⊢T κ → K₂ ⊢T κ
subst-Type σ (var x) = σ x
subst-Type σ (Bool l x) = Bool (subst-Type σ l) (subst-Type σ x)
subst-Type σ (Num x) = Num (subst-Type σ x)
subst-Type σ (A ⇒ B) = (subst-Type σ A) ⇒ (subst-Type σ B)
subst-Type σ (Index A) = Index (subst-Type σ A)
subst-Type σ (Array A B) = Array (subst-Type σ A) (subst-Type σ B)
subst-Type σ (Forall s A) = Forall s (subst-Type (binder σ) A)
subst-Type σ [ n ] = [ n ]
subst-Type σ const = const
subst-Type σ linear = linear
subst-Type σ U = U
subst-Type σ Ex = Ex
subst-Type σ (MaxLin l₁ l₂ l₃) = MaxLin (subst-Type σ l₁) (subst-Type σ l₂) (subst-Type σ l₃)
subst-Type σ (MaxPol p₁ p₂ p₃) = MaxPol (subst-Type σ p₁) (subst-Type σ p₂) (subst-Type σ p₃)
subst-Type σ (HasMul l₁ l₂ l₃) = HasMul (subst-Type σ l₁) (subst-Type σ l₂) (subst-Type σ l₃)
subst-Type σ (NegPol p₁ p₂)    = NegPol (subst-Type σ p₁) (subst-Type σ p₂)
subst-Type σ (Quantify p₁ p₂)  = Quantify (subst-Type σ p₁) (subst-Type σ p₂)

single-sub : ∀ {K κ} → K ⊢T κ → K ⇒ₛ (K ,- κ)
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
           (s : SmallKind κ) →
           (Δ ,- κ) / (ren-Context wk Γ) ⊢ A →
           Δ / Γ ⊢ Forall s A
  _•_    : ∀ {Δ Γ κ s A} →
           Δ / Γ ⊢ Forall s A →
           (B : Δ ⊢T κ) →
           Δ / Γ ⊢ subst-Type (single-sub B) A

  -- External functions
  func   : ∀ {Δ Γ} → Δ / Γ ⊢ Num linear → Δ / Γ ⊢ Num linear

  const  : ∀ {Δ Γ} → ℚ → Δ / Γ ⊢ Num const
  _`+_   : ∀ {Δ Γ l₁ l₂ l₃} → Δ / Γ ⊢ MaxLin l₁ l₂ l₃ → Δ / Γ ⊢ Num l₁ → Δ / Γ ⊢ Num l₂ → Δ / Γ ⊢ Num l₃
  _`*_   : ∀ {Δ Γ l₁ l₂ l₃} → Δ / Γ ⊢ HasMul l₁ l₂ l₃ → Δ / Γ ⊢ Num l₁ → Δ / Γ ⊢ Num l₂ → Δ / Γ ⊢ Num l₃

  -- Arrays
  array   : ∀ {Δ Γ} → (n : Δ ⊢T Nat) (A : Δ ⊢T Type) → Δ / (Γ ,- Index n) ⊢ A → Δ / Γ ⊢ Array n A
  index   : ∀ {Δ Γ} → (n : Δ ⊢T Nat) (A : Δ ⊢T Type) → Δ / Γ ⊢ Array n A → Δ / Γ ⊢ Index n → Δ / Γ ⊢ A
  idx     : ∀ {Δ Γ n} → (i : Fin n) → Δ / Γ ⊢ Index [ n ]
  -- FIXME: crush/fold/reduce
  -- FIXME: rename to foreach, etc.

  -- Comparisons
  _`≤_   : ∀ {Δ Γ l₁ l₂ l₃} → Δ / Γ ⊢ MaxLin l₁ l₂ l₃ → Δ / Γ ⊢ Num l₁ → Δ / Γ ⊢ Num l₂ → Δ / Γ ⊢ Bool l₃ U

  -- Polymorphic if-then-else
  if_then_else_ : ∀ {Δ Γ A}
     (cond : Δ / Γ ⊢ Bool linear U)
     (on-true on-false : Δ / Γ ⊢ A) →
     Δ / Γ ⊢ A
  -- FIXME: need an 'almost equal' typeclass constraint here; can make it as complex as needed
  -- Soundness counterexample: forall (x : Rat) . f 10 ! (if (x >= 7) then 0 else 1) == 0

  -- Logic
  `¬_     : ∀ {Δ Γ l p₁ p₂} →
            Δ / Γ ⊢ NegPol p₁ p₂ →
            Δ / Γ ⊢ Bool l p₁ →
            Δ / Γ ⊢ Bool l p₂
  _`∧_ _`∨_ : ∀ {Δ Γ l₁ l₂ l₃ p₁ p₂ p₃} →
            Δ / Γ ⊢ MaxLin l₁ l₂ l₃ →
            Δ / Γ ⊢ MaxPol p₁ p₂ p₃ →
            Δ / Γ ⊢ Bool l₁ p₁ →
            Δ / Γ ⊢ Bool l₂ p₂ →
            Δ / Γ ⊢ Bool l₃ p₃

--   constraint : ∀ {Δ Γ} → Δ / Γ ⊢ Bool constraint → Δ / Γ ⊢ Bool query
  ∃          : ∀ {Δ Γ p₁ p₂ l} → Δ / Γ ⊢ Quantify p₁ p₂ → Δ / Γ ⊢ (Num linear ⇒ Bool l p₁) → Δ / Γ ⊢ Bool l p₂
