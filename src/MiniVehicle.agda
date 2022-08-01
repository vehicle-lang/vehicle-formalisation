{-# OPTIONS --postfix-projections --safe #-}

module MiniVehicle where

open import Data.Rational using (ℚ)

data Linearity : Set where
  const linear : Linearity

data BoolKind : Set where
  constraint {- universal existential query -} : BoolKind

{-
data QueryKind : Set where
  universal existential : QueryKind

queryKind : QueryKind → BoolKind
queryKind universal   = universal
queryKind existential = existential
-}

data Kind : Set where
  Nat Type : Kind

data KindContext : Set where
  ε     : KindContext
  _,-ℕ : KindContext → KindContext

data _⊢T_ : KindContext → Kind → Set where
  Bool   : ∀ {Δ} → BoolKind → Δ ⊢T Type
  Num    : ∀ {Δ} → Linearity → Δ ⊢T Type
  _⇒_   : ∀ {Δ} → Δ ⊢T Type → Δ ⊢T Type → Δ ⊢T Type
{- TODO:
  Array  : ℕ → Type → Type
  Index  : ℕ → Type
-}

data Context : KindContext → Set where
  ε    : ∀ {Δ} → Context Δ
  _,-_ : ∀ {Δ} → Context Δ → Δ ⊢T Type → Context Δ

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

  -- External functions
  func   : ∀ {Δ Γ} →
           Δ / Γ ⊢ Num linear →
           Δ / Γ ⊢ Num linear

  const  : ∀ {Δ Γ} → ℚ → Δ / Γ ⊢ Num const
  lift   : ∀ {Δ Γ} → Δ / Γ ⊢ Num const → Δ / Γ ⊢ Num linear
  _`+_   : ∀ {Δ Γ} → Δ / Γ ⊢ Num linear → Δ / Γ ⊢ Num linear → Δ / Γ ⊢ Num linear
  _`*_   : ∀ {Δ Γ} → Δ / Γ ⊢ Num const → Δ / Γ ⊢ Num linear → Δ / Γ ⊢ Num linear

  -- Comparisons
  _`≤_   : ∀ {Δ Γ} → Δ / Γ ⊢ Num linear → Δ / Γ ⊢ Num linear → Δ / Γ ⊢ Bool constraint

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
