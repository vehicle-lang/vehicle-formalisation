{-# OPTIONS --postfix-projections --safe #-}

module MiniVehicle.Language.Syntax.Kind where


-- Kinds

data Kind : Set where
  Nat     : Kind
  Type    : Kind
  NumRes  : Kind
  BoolRes : Kind

variable κ κ′ : Kind

data is-small : Kind → Set where
  Nat     : is-small Nat
  NumRes  : is-small NumRes
  BoolRes : is-small BoolRes

infixl 10 _,-_


-- Kind contexts

data KindContext : Set where
  ε    : KindContext
  _,-_ : KindContext → Kind → KindContext

variable Δ Δ′ : KindContext
