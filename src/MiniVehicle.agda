{-# OPTIONS --postfix-projections --safe #-}

module MiniVehicle where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Rational using (ℚ)

data Linearity : Set where
  const linear : Linearity

data BoolKind : Set where
  constraint query : BoolKind

data Kind : Set where
  Nat Type : Kind

data KindContext : Set where
  ε     : KindContext
  _,-ℕ : KindContext → KindContext

data _⊢Tv : KindContext → Set where
  zero : ∀ {Δ} → (Δ ,-ℕ) ⊢Tv
  succ : ∀ {Δ} → Δ ⊢Tv → (Δ ,-ℕ) ⊢Tv

_⇒ᵣ_ : KindContext → KindContext → Set
K₁ ⇒ᵣ K₂ = K₂ ⊢Tv → K₁ ⊢Tv

under : ∀ {K₁ K₂} → (K₁ ⇒ᵣ K₂) → (K₁ ,-ℕ) ⇒ᵣ (K₂ ,-ℕ)
under ρ zero     = zero
under ρ (succ x) = succ (ρ x)

wk : ∀ {K} → (K ,-ℕ) ⇒ᵣ K
wk = succ

data _⊢T_ : KindContext → Kind → Set where
  var    : ∀ {Δ} → Δ ⊢Tv → Δ ⊢T Nat
  Bool   : ∀ {Δ} → BoolKind → Δ ⊢T Type
  Num    : ∀ {Δ} → Linearity → Δ ⊢T Type
  _⇒_   : ∀ {Δ} → Δ ⊢T Type → Δ ⊢T Type → Δ ⊢T Type
  Index  : ∀ {Δ} → Δ ⊢T Nat → Δ ⊢T Type
  Array  : ∀ {Δ} → Δ ⊢T Nat → Δ ⊢T Type → Δ ⊢T Type
  Forall : ∀ {Δ} → (Δ ,-ℕ) ⊢T Type → Δ ⊢T Type
  [_]    : ∀ {Δ} → ℕ → Δ ⊢T Nat

ren-Type : ∀ {K₁ K₂ κ} → (K₂ ⇒ᵣ K₁) → K₁ ⊢T κ → K₂ ⊢T κ
ren-Type ρ (var x) = var (ρ x)
ren-Type ρ (Bool x) = Bool x
ren-Type ρ (Num x) = Num x
ren-Type ρ (A ⇒ B) = (ren-Type ρ A) ⇒ (ren-Type ρ B)
ren-Type ρ (Index A) = Index (ren-Type ρ A)
ren-Type ρ (Array A B) = Array (ren-Type ρ A) (ren-Type ρ B)
ren-Type ρ (Forall A) = Forall (ren-Type (under ρ) A)
ren-Type ρ [ n ] = [ n ]

binder : ∀ {K₁ K₂} → (K₁ ⊢Tv → K₂ ⊢T Nat) → ((K₁ ,-ℕ)  ⊢Tv → (K₂ ,-ℕ) ⊢T Nat)
binder σ zero     = var zero
binder σ (succ x) = ren-Type wk (σ x)

subst-Type : ∀ {K₁ K₂ κ} → (K₁ ⊢Tv → K₂ ⊢T Nat) → K₁ ⊢T κ → K₂ ⊢T κ
subst-Type σ (var x) = σ x
subst-Type σ (Bool x) = Bool x
subst-Type σ (Num x) = Num x
subst-Type σ (A ⇒ B) = (subst-Type σ A) ⇒ (subst-Type σ B)
subst-Type σ (Index A) = Index (subst-Type σ A)
subst-Type σ (Array A B) = Array (subst-Type σ A) (subst-Type σ B)
subst-Type σ (Forall A) = Forall (subst-Type (binder σ) A)
subst-Type σ [ n ] = [ n ]

single-sub : ∀ {K} → K ⊢T Nat → (K ,-ℕ) ⊢Tv → K ⊢T Nat
single-sub N zero = N
single-sub N (succ x) = var x

data Context : KindContext → Set where
  ε    : ∀ {Δ} → Context Δ
  _,-_ : ∀ {Δ} → Context Δ → Δ ⊢T Type → Context Δ

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
  Λ      : ∀ {Δ Γ A} →
           (Δ ,-ℕ) / (ren-Context wk Γ) ⊢ A →
           Δ / Γ ⊢ Forall A
  _•_    : ∀ {Δ Γ A} →
           Δ / Γ ⊢ Forall A →
           (N : Δ ⊢T Nat) →
           Δ / Γ ⊢ subst-Type (single-sub N) A

  -- External functions
  func   : ∀ {Δ Γ} →
           Δ / Γ ⊢ Num linear →
           Δ / Γ ⊢ Num linear

  const  : ∀ {Δ Γ} → ℚ → Δ / Γ ⊢ Num const
  lift   : ∀ {Δ Γ} → Δ / Γ ⊢ Num const → Δ / Γ ⊢ Num linear
  _`+_   : ∀ {Δ Γ} → Δ / Γ ⊢ Num linear → Δ / Γ ⊢ Num linear → Δ / Γ ⊢ Num linear
  _`*_   : ∀ {Δ Γ} → Δ / Γ ⊢ Num const → Δ / Γ ⊢ Num linear → Δ / Γ ⊢ Num linear

  -- Arrays
  array   : ∀ {Δ Γ} → (n : Δ ⊢T Nat) (A : Δ ⊢T Type) → Δ / (Γ ,- Index n) ⊢ A → Δ / Γ ⊢ Array n A
  index   : ∀ {Δ Γ} → (n : Δ ⊢T Nat) (A : Δ ⊢T Type) → Δ / Γ ⊢ Array n A → Δ / Γ ⊢ Index n → Δ / Γ ⊢ A
  idx     : ∀ {Δ Γ n} → (i : Fin n) → Δ / Γ ⊢ Index [ n ]
  -- FIXME: crush/fold/reduce

  -- Comparisons
  _`≤_   : ∀ {Δ Γ} → Δ / Γ ⊢ Num linear → Δ / Γ ⊢ Num linear → Δ / Γ ⊢ Bool constraint

  -- Polymorphic if-then-else
  if_then_else_ : ∀ {Δ Γ A}
     (cond : Δ / Γ ⊢ Bool constraint)
     (on-true on-false : Δ / Γ ⊢ A) →
     Δ / Γ ⊢ A

  -- Logic
  `¬_     : ∀ {Δ Γ} → Δ / Γ ⊢ Bool constraint → Δ / Γ ⊢ Bool constraint
  _`∧_    : ∀ {Δ Γ} → Δ / Γ ⊢ Bool constraint → Δ / Γ ⊢ Bool constraint → Δ / Γ ⊢ Bool constraint
  _`∨_    : ∀ {Δ Γ} → Δ / Γ ⊢ Bool constraint → Δ / Γ ⊢ Bool constraint → Δ / Γ ⊢ Bool constraint

{-
  universal   : ∀ {Γ} → Γ ⊢ Bool constraint → Γ ⊢ Bool universal
  existential : ∀ {Γ} → Γ ⊢ Bool constraint → Γ ⊢ Bool existential

  forAll  : ∀ {Γ} → (Γ ,- Num linear) ⊢ Bool universal   → Γ ⊢ Bool universal
  exists  : ∀ {Γ} → (Γ ,- Num linear) ⊢ Bool existential → Γ ⊢ Bool existential
  query   : ∀ {Γ} → (k : QueryKind) → Γ ⊢ Bool (queryKind k) → Γ ⊢ Bool query
-}
