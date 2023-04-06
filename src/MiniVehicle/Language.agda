{-# OPTIONS --postfix-projections --safe #-}

open import MiniVehicle.Language.SyntaxRestriction

module MiniVehicle.Language (R : SyntaxRestriction) where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Rational using (ℚ)

open SyntaxRestriction R

data Kind : Set where
  Nat Type NumRes BoolRes : Kind

data SmallKind : Kind → Set where
  Nat    : SmallKind Nat
  NumRes : SmallKind NumRes
  BoolRes : SmallKind BoolRes

data KindContext : Set where
  ε    : KindContext
  _,-_ : KindContext → Kind → KindContext

private variable Δ : KindContext
    
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
  var    : ∀ {κ} → Δ ⊢Tv κ → Δ ⊢T κ
  _⇒_   : Δ ⊢T Type → Δ ⊢T Type → Δ ⊢T Type
  Forall : ∀ {κ} → SmallKind κ → (Δ ,- κ) ⊢T Type → Δ ⊢T Type

  Bool   : Δ ⊢T BoolRes → Δ ⊢T Type
  Num    : Δ ⊢T NumRes → Δ ⊢T Type

  Index  : Δ ⊢T Nat → Δ ⊢T Type
  Vec    : Δ ⊢T Nat → Δ ⊢T Type → Δ ⊢T Type
  [_]    : ℕ → Δ ⊢T Nat

  NumRes : NumRestriction → Δ ⊢T NumRes
  NumConstRes : Δ ⊢T NumRes → Δ ⊢T Type
  FuncRes     : Δ ⊢T NumRes → Δ ⊢T NumRes → Δ ⊢T Type
  AddRes      : Δ ⊢T NumRes → Δ ⊢T NumRes → Δ ⊢T NumRes → Δ ⊢T Type
  MulRes      : Δ ⊢T NumRes → Δ ⊢T NumRes → Δ ⊢T NumRes → Δ ⊢T Type
  
  BoolRes  : BoolRestriction → Δ ⊢T BoolRes
  BoolConstRes : Δ ⊢T BoolRes → Δ ⊢T Type
  NotRes       : Δ ⊢T BoolRes → Δ ⊢T BoolRes → Δ ⊢T Type
  AndRes       : Δ ⊢T BoolRes → Δ ⊢T BoolRes → Δ ⊢T BoolRes → Δ ⊢T Type
  OrRes        : Δ ⊢T BoolRes → Δ ⊢T BoolRes → Δ ⊢T BoolRes → Δ ⊢T Type
  LeqRes       : Δ ⊢T NumRes → Δ ⊢T NumRes → Δ ⊢T BoolRes → Δ ⊢T Type
  QuantRes     : Δ ⊢T NumRes → Δ ⊢T BoolRes → Δ ⊢T BoolRes → Δ ⊢T Type
  IfRes        : Δ ⊢T BoolRes → Δ ⊢T Type

ren-Type : ∀ {K₁ K₂ κ} → (K₂ ⇒ᵣ K₁) → K₁ ⊢T κ → K₂ ⊢T κ
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
ren-Type ρ (LeqRes p₁ p₂ p₃) = LeqRes (ren-Type ρ p₁) (ren-Type ρ p₂) (ren-Type ρ p₃)
ren-Type ρ (NotRes p₁ p₂)  = NotRes (ren-Type ρ p₁) (ren-Type ρ p₂)
ren-Type ρ (QuantRes l p₁ p₂)  = QuantRes (ren-Type ρ l) (ren-Type ρ p₁) (ren-Type ρ p₂)
ren-Type ρ (IfRes p)  = IfRes (ren-Type ρ p)


_⇒ₛ_ : KindContext → KindContext → Set
K₁ ⇒ₛ K₂ = ∀ {κ} → K₂ ⊢Tv κ → K₁ ⊢T κ

binder : ∀ {K₁ K₂} → (K₂ ⇒ₛ K₁) → ∀ {κ} → (K₂ ,- κ) ⇒ₛ (K₁ ,- κ)
binder σ zero     = var zero
binder σ (succ x) = ren-Type wk (σ x)

subst-Type : ∀ {K₁ K₂} → (K₂ ⇒ₛ K₁) → ∀ {κ} → K₁ ⊢T κ → K₂ ⊢T κ
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
subst-Type σ (LeqRes p₁ p₂ p₃) = LeqRes (subst-Type σ p₁) (subst-Type σ p₂) (subst-Type σ p₃)
subst-Type σ (NotRes p₁ p₂)  = NotRes (subst-Type σ p₁) (subst-Type σ p₂)
subst-Type σ (QuantRes l p₁ p₂)  = QuantRes (subst-Type σ l) (subst-Type σ p₁) (subst-Type σ p₂)
subst-Type σ (IfRes p)  = IfRes (subst-Type σ p)

single-sub : ∀ {K κ} → K ⊢T κ → K ⇒ₛ (K ,- κ)
single-sub N zero = N
single-sub N (succ x) = var x

data Context : KindContext → Set where
  ε    : Context Δ
  _,-_ : Context Δ → Δ ⊢T Type → Context Δ

infixl 10 _,-_

private variable Γ : Context Δ

ren-Context : ∀ {K₁ K₂} → (K₂ ⇒ᵣ K₁) → Context K₁ → Context K₂
ren-Context ρ ε        = ε
ren-Context ρ (Γ ,- A) = (ren-Context ρ Γ) ,- ren-Type ρ A

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
           (s : SmallKind κ) →
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
  _`≤_   : ∀ {l₁ l₂ l₃} → Δ / Γ ⊢ LeqRes l₁ l₂ l₃ → Δ / Γ ⊢ Num l₁ → Δ / Γ ⊢ Num l₂ → Δ / Γ ⊢ Bool l₃

  -- Polymorphic if-then-else
  if_then_else_ : ∀ {A r₁} → Δ / Γ ⊢ IfRes r₁ → 
     (cond : Δ / Γ ⊢ Bool r₁)
     (on-true on-false : Δ / Γ ⊢ A) →
     Δ / Γ ⊢ A
  -- FIXME: need an 'almost equal' typeclass constraint here; can make it as complex as needed
  -- Soundness counterexample: forall (x : Rat) . f 10 ! (if (x >= 7) then 0 else 1) == 0

  -- Logic
  _`∧_ : ∀ {r₁ r₂ r₃} → Δ / Γ ⊢ AndRes r₁ r₂ r₃ → Δ / Γ ⊢ Bool r₁ → Δ / Γ ⊢ Bool r₂ → Δ / Γ ⊢ Bool r₃
  _`∨_ : ∀ {b₁ b₂ b₃} → Δ / Γ ⊢ OrRes b₁ b₂ b₃ → Δ / Γ ⊢ Bool b₁ →
            Δ / Γ ⊢ Bool b₂ →
            Δ / Γ ⊢ Bool b₃
  `¬_ : ∀ {b₁ b₂} → Δ / Γ ⊢ NotRes b₁ b₂ → Δ / Γ ⊢ Bool b₁ →
        Δ / Γ ⊢ Bool b₂
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
  leqRes : ∀ {n₁ n₂ b} → LeqRestriction n₁ n₂ b →
           Δ / Γ ⊢ LeqRes (NumRes n₁) (NumRes n₂) (BoolRes b)
  quantRes : ∀ {n p₁ p₂} → QuantRestriction n p₁ p₂ →
             Δ / Γ ⊢ QuantRes (NumRes n) (BoolRes p₁) (BoolRes p₂)
  ifRes : ∀ {b} → IfRestriction b →
          Δ / Γ ⊢ IfRes (BoolRes b)
