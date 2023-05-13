{-# OPTIONS --postfix-projections #-}

module StandardSemantics where

open import Level using (0ℓ; suc)
open import Data.Bool using (true; false; _∧_; _∨_; not) renaming (Bool to 𝔹; T to True)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Rational using (ℚ; _≤ᵇ_) renaming (_+_ to _+ℚ_; _*_ to _*ℚ_)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym; cong₂)

open import MiniVehicle.Qualifiers
open import Interpretation

data Quant (A : Set) : Set where
  return : A → Quant A
  _and_  : Quant A → Quant A → Quant A
  _or_   : Quant A → Quant A → Quant A
  ex     : (ℚ → Quant A) → Quant A

eval-Quant : ∀ {A} → Quant A → (A → Set) → Set
eval-Quant (return x) k = k x
eval-Quant (ex x)     k = Σ[ q ∈ ℚ ] eval-Quant (x q) k
eval-Quant (x and y) k = (eval-Quant x k) × (eval-Quant y k)
eval-Quant (x or y) k = (eval-Quant x k) ⊎ (eval-Quant y k)

module _ (extFunc : ℚ → ℚ) where
  open Model

  ℳ : Model verifierRestriction (suc 0ℓ) 0ℓ
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
  ℳ .⟦add⟧ (_ , x , y)  = x +ℚ y
  ℳ .⟦mul⟧ (_ , x , y)  = x *ℚ y
  ℳ .⟦const⟧ q _ = q
  ℳ .⟦extFunc⟧ (_ , v)  = extFunc v
  ℳ .⟦Bool⟧ (_ , U) = 𝔹
  ℳ .⟦Bool⟧ (_ , Ex) = Quant 𝔹
  ℳ .⟦not⟧ (notRes U , x) = not x
  ℳ .⟦and⟧ (maxBoolRes _ U-U , x , y) = x ∧ y
  ℳ .⟦and⟧ (maxBoolRes _ U-Ex , x , y) = (return x) and y
  ℳ .⟦and⟧ (maxBoolRes _ Ex-U , x , y) = x and (return y)
  ℳ .⟦and⟧ (maxBoolRes _ Ex-Ex , x , y) = x and y
  ℳ .⟦or⟧ (maxBoolRes _ U-U , x , y) = x ∨ y
  ℳ .⟦or⟧ (maxBoolRes _ U-Ex , x , y) = (return x) or y
  ℳ .⟦or⟧ (maxBoolRes _ Ex-U , x , y) = x or (return y)
  ℳ .⟦or⟧ (maxBoolRes _ Ex-Ex , x , y) = x or y
  ℳ .⟦≤⟧ (leqRes _ , q₁ , q₂) = q₁  ≤ᵇ q₂
  ℳ .⟦if⟧ ((tr , fa) , (ifRes _ , true)) = tr
  ℳ .⟦if⟧ ((tr , fa) , (ifRes _ , false)) = fa
  ℳ .⟦Index⟧ i = Fin i
  ℳ .⟦idx⟧ _ i _  = i
  ℳ .⟦∃⟧ (quantRes U , f) = ex (λ q → return (f q))
  ℳ .⟦∃⟧ (quantRes Ex , f) = ex f
