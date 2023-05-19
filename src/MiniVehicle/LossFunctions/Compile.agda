
module MiniVehicle.LossFunctions.Compile where

open import Data.Fin
open import Data.Empty
open import Data.Product
open import Data.Unit
open import Data.Bool renaming (Bool to 𝔹)
open import Level as Level using (0ℓ)
open import Function.Base as Function using ()
open import Data.Rational as ℚ

open import MiniVehicle.Language.SyntaxRestriction


lossRestriction : SyntaxRestriction
lossRestriction = record
  { SyntaxRestriction noRestriction
  ; IfRestriction = λ _ → ⊥
  }

open import MiniVehicle.Language.Interpretation lossRestriction

module _ (extFunc : ℚ → ℚ) (max : (ℚ → ℚ) → ℚ) where

  open Model

  ℳ : Model (Level.suc 0ℓ) 0ℓ
  ℳ .⟦Type⟧ = Set
  ℳ ._==>_ X Y = X → Y
  ℳ .Flat X = X
  ℳ .elem a x = a
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
  ℳ .⟦add⟧ (_ , x , y)  = x ℚ.+ y
  ℳ .⟦mul⟧ (_ , x , y)  = x ℚ.* y
  ℳ .⟦const⟧ q _ = q
  ℳ .⟦extFunc⟧ (_ , v)  = extFunc v
  ℳ .⟦Bool⟧ _ = ℚ
  ℳ .⟦not⟧ (_ , x) = ℚ.- x
  ℳ .⟦and⟧ (_ , x , y) = x ℚ.⊓ y
  ℳ .⟦or⟧ (_ , x , y) = x ℚ.⊔ y
  ℳ .⟦≤⟧ (_ , x , y) = x ℚ.- y
  ℳ .⟦if⟧ ((tr , fa) , (() , _))
  ℳ .⟦Index⟧ i = Fin i
  ℳ .⟦idx⟧ _ i _  = i
  ℳ .⟦∃⟧ (_ , f) = max f

  module 𝒩 = Interpret ℳ
  open import MiniVehicle.Language lossRestriction

  compile : ε / ε ⊢ Bool (BoolRes tt) → ℚ
  compile t = 𝒩.⟦ t ⟧tm _ tt
