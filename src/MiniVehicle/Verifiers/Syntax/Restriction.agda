{-# OPTIONS --safe #-}

module MiniVehicle.Verifiers.Syntax.Restriction where

open import Data.Product

open import MiniVehicle.Language.Syntax.Restriction

-- Linearity restrictions

data LinearityVal : Set where
  const linear nonlinear : LinearityVal

data NumConstRel : LinearityVal → Set where
  const : NumConstRel const

data FuncRel : LinearityVal → LinearityVal → Set where
  linear-linear : FuncRel linear linear

data MaxLinRel : LinearityVal → LinearityVal → LinearityVal → Set where
  const-const   : MaxLinRel const const const
  const-linear  : MaxLinRel const linear linear
  linear-const  : MaxLinRel linear const linear
  linear-linear : MaxLinRel linear linear linear

data MulLinRel : LinearityVal → LinearityVal → LinearityVal → Set where
  const-const  : MulLinRel const const const
  const-linear : MulLinRel const linear linear
  linear-const : MulLinRel linear const linear

-- Restrictions

data BoolConstRel : LinearityVal × PolarityVal → Set where
  U : BoolConstRel (const , U)

data MaxBoolRes : LinearityVal × PolarityVal → LinearityVal × PolarityVal → LinearityVal × PolarityVal → Set where
  maxBoolRes : ∀ {l₁ l₂ l₃ p₁ p₂ p₃} → MaxLinRel l₁ l₂ l₃ → MaxPolRel p₁ p₂ p₃ → MaxBoolRes (l₁ , p₁) (l₂ , p₂) (l₃ , p₃)

data NotRes : LinearityVal × PolarityVal → LinearityVal × PolarityVal → Set where
  notRes : ∀ {l p₁ p₂} → NegPolRel p₁ p₂ → NotRes (l , p₁) (l , p₂)

data LeqRes : LinearityVal → LinearityVal → LinearityVal × PolarityVal → Set where
  leqRes : ∀ {l₁ l₂ l₃} → MaxLinRel l₁ l₂ l₃ → LeqRes l₁ l₂ (l₃ , U)

data IfRes : LinearityVal × PolarityVal → Set where
  ifRes : ∀ l → IfRes (l , U)

data QuantRes : LinearityVal → LinearityVal × PolarityVal → LinearityVal × PolarityVal → Set where
  quantRes : ∀ {l p₁ p₂} → QuantifyRel p₁ p₂ → QuantRes linear (l , p₁) (l , p₂)

-- Restrictions

verifierRestriction : Restriction
verifierRestriction = record
  { NumRestriction  = LinearityVal
  ; BoolRestriction = LinearityVal × PolarityVal

  ; BoolConstRestriction = BoolConstRel
  ; AndRestriction = MaxBoolRes
  ; OrRestriction  = MaxBoolRes
  ; NotRestriction = NotRes
  ; LeqRestriction = LeqRes
  ; QuantRestriction = QuantRes
  ; IfRestriction = IfRes

  ; NumConstRestriction = NumConstRel
  ; FuncRestriction = FuncRel
  ; AddRestriction = MaxLinRel
  ; MulRestriction = MulLinRel
  }
