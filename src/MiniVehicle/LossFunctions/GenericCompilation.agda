module MiniVehicle.LossFunctions.GenericCompilation where

open import Data.Fin
open import Data.Empty
open import Data.Product
open import Data.Unit
open import Data.Bool renaming (Bool to 𝔹)
open import Level as Level using (0ℓ)
open import Function.Base as Function using ()
open import Data.Rational as ℚ

open import MiniVehicle.Language.Syntax.Restriction
import MiniVehicle.Language.StandardSemantics as S
open S.Quant
open import MiniVehicle.LossFunctions.GenericDifferentiableLogic

lossRestriction : Restriction
lossRestriction = record
  { Restriction defaultRestriction
  ; IfRestriction = λ _ → ⊥
  }

open import MiniVehicle.Language.Interpretation lossRestriction

module _ (extFunc : ℚ → ℚ) (dl : DifferentiableLogic) where

  open Model
  open DifferentiableLogic dl

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
  ℳ .⟦Bool⟧ U = ⟪Bool⟫
  ℳ .⟦Bool⟧ Ex = S.Quant ⟪Bool⟫
  ℳ .⟦not⟧ (U , x) = ⟪not⟫ x   -- swap
  ℳ .⟦and⟧ (U-U , x , y) = x ⟪and⟫ y 
  ℳ .⟦and⟧ (U-Ex , x , y) = (return x) and y
  ℳ .⟦and⟧ (Ex-U , x , y) = x and (return y)
  ℳ .⟦and⟧ (Ex-Ex , x , y) = x and y
  ℳ .⟦or⟧ (U-U , x , y) = x ⟪or⟫ y
  ℳ .⟦or⟧ (U-Ex , x , y) = (return x) or y
  ℳ .⟦or⟧ (Ex-U , x , y) = x or (return y)
  ℳ .⟦or⟧ (Ex-Ex , x , y) = x or y
  ℳ .⟦≤⟧ (U , x , y) = x ⟪≤⟫ y
  ℳ .⟦<⟧ (U , x , y) = x ⟪<⟫ y
  ℳ .⟦if⟧ ((tr , fa) , (() , _))
  ℳ .⟦Index⟧ i = Fin i
  ℳ .⟦idx⟧ _ i _  = i
  ℳ .⟦∃⟧ (U , f) = ex (λ q → return (f q))
  ℳ .⟦∃⟧ (Ex , f) = ex f

  module 𝒩 = Interpret ℳ
  open import MiniVehicle.Language.Syntax lossRestriction

  compile : ∀ {t} → ε / ε ⊢ t → 𝒩.⟦ t ⟧ty _
  compile t = 𝒩.⟦ t ⟧tm _ tt
