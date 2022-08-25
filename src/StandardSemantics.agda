{-# OPTIONS --postfix-projections #-} -- --safe #-}

module StandardSemantics where

open import Level using (Lift; lift; lower; 0ℓ; suc)
open import Data.Bool using (true; false; _∧_; _∨_; not)
                   renaming (Bool to 𝔹; if_then_else_ to ifᵇ_then_else_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; _≤ᵇ_) renaming (_+_ to _+ℚ_; _*_ to _*ℚ_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym; cong₂)

open import MiniVehicle
open import Interpretation

module _ (extFunc : ℚ → ℚ) where
  open Model

  ℳ : Model (suc 0ℓ) 0ℓ
  ℳ .⟦Type⟧ = Set
  ℳ ._==>_ X Y = X → Y
  ℳ .⟦id⟧ = λ x → x
  ℳ ._∘_ f g x = f (g x)
  ℳ ._⟦×⟧_ = _×_
  ℳ .⟦⊤⟧ = ⊤
  ℳ .⟦terminal⟧ x = tt
  ℳ .⟦proj₁⟧ = proj₁
  ℳ .⟦proj₂⟧ = proj₂
  ℳ .⟨_,_⟩ f g x = f x , g x
  ℳ ._⟦⇒⟧_ X Y = X → Y
  ℳ .⟦Λ⟧ f x y = f (x , y)
  ℳ .⟦eval⟧ (f , x) = f x
  ℳ .⟦∀⟧ A = ∀ n → A n
  ℳ .⟦∀-intro⟧ f x n = f n x
  ℳ .⟦∀-elim⟧ n f = f n
  ℳ .Mon X = X
  ℳ .⟦return⟧ x = x
  ℳ .⟦extend⟧ f = f
  ℳ .⟦Num⟧ _ = ℚ
  ℳ .⟦add⟧ (x , y) = x +ℚ y
  ℳ .⟦mul⟧ (x , y) = x *ℚ y
  ℳ .⟦num⟧ q _ = q
  ℳ .⟦const⟧ q = q
  ℳ .⟦extFunc⟧ = extFunc
  ℳ .⟦Bool⟧ _ = 𝔹
  ℳ .⟦not⟧ = not
  ℳ .⟦and⟧ (x , y) = x ∧ y
  ℳ .⟦or⟧ (x , y) = x ∨ y
  ℳ .⟦≤⟧ (q₁ , q₂) = q₁ ≤ᵇ q₂
  ℳ .⟦if⟧ ((tr , fa) , false) = fa
  ℳ .⟦if⟧ ((tr , fa) , true) = tr
  ℳ .⟦Index⟧ = Fin
  ℳ .⟦idx⟧ _ i _ = i

  module ℐ = Interpret ℳ
