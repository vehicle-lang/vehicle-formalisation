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

data Type : Set where
  Bool   : BoolKind → Type
  Num    : Linearity → Type
  _⇒_   : Type → Type → Type
{- TODO:
  Array  : ℕ → Type → Type
  Index  : ℕ → Type
-}

data Context : Set where
  ε    : Context
  _,-_ : Context → Type → Context

data _∋_ : Context → Type → Set where
  zero : ∀ {Γ A}   →         (Γ ,- A) ∋ A
  succ : ∀ {Γ A B} → Γ ∋ A → (Γ ,- B) ∋ A

data _⊢_ : Context → Type → Set where
  -- Variables
  var    : ∀ {Γ A} → Γ ∋ A → Γ ⊢ A

  -- Functions
  ƛ      : ∀ {Γ A B} → (Γ ,- A) ⊢ B → Γ ⊢ (A ⇒ B)
  _∙_    : ∀ {Γ A B} → Γ ⊢ (A ⇒ B) → Γ ⊢ A → Γ ⊢ B

  -- FIXME: named functions
--  func   : ∀ {Γ} → Γ ⊢ Num linear → Γ ⊢ Num linear

  const  : ∀ {Γ} → ℚ → Γ ⊢ Num const
  lift   : ∀ {Γ} → Γ ⊢ Num const → Γ ⊢ Num linear
  _`+_   : ∀ {Γ} → Γ ⊢ Num linear → Γ ⊢ Num linear → Γ ⊢ Num linear
  _`*_   : ∀ {Γ} → Γ ⊢ Num const → Γ ⊢ Num linear → Γ ⊢ Num linear

  -- Comparisons
  _`≤_   : ∀ {Γ} → Γ ⊢ Num linear → Γ ⊢ Num linear → Γ ⊢ Bool constraint

  if_then_else_ : ∀ {Γ A}
     (cond : Γ ⊢ Bool constraint) (on-true on-false : Γ ⊢ A) →
     Γ ⊢ A

  -- Logic
  `¬_     : ∀ {Γ} → Γ ⊢ Bool constraint → Γ ⊢ Bool constraint
  _`∧_    : ∀ {Γ} → Γ ⊢ Bool constraint → Γ ⊢ Bool constraint → Γ ⊢ Bool constraint
  _`∨_    : ∀ {Γ} → Γ ⊢ Bool constraint → Γ ⊢ Bool constraint → Γ ⊢ Bool constraint

{-
  universal   : ∀ {Γ} → Γ ⊢ Bool constraint → Γ ⊢ Bool universal
  existential : ∀ {Γ} → Γ ⊢ Bool constraint → Γ ⊢ Bool existential

  forAll  : ∀ {Γ} → (Γ ,- Num linear) ⊢ Bool universal   → Γ ⊢ Bool universal
  exists  : ∀ {Γ} → (Γ ,- Num linear) ⊢ Bool existential → Γ ⊢ Bool existential
  query   : ∀ {Γ} → (k : QueryKind) → Γ ⊢ Bool (queryKind k) → Γ ⊢ Bool query
-}
