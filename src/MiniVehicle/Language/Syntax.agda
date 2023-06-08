{-# OPTIONS --postfix-projections --safe #-}

open import MiniVehicle.Language.Syntax.Restriction

module MiniVehicle.Language.Syntax (R : Restriction) where

open import MiniVehicle.Language.Syntax.Kind   public
open import MiniVehicle.Language.Syntax.Type R public
open import MiniVehicle.Language.Syntax.Term R public
