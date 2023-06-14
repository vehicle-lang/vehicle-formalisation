
module MiniVehicle.Language.StandardSemantics where

open import Level using (0ℓ; suc)
open import Data.Bool using (true; false; _∧_; _∨_; not) renaming (Bool to 𝔹; T to True)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product as Prod using (Σ; _×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Rational using (ℚ; _≤ᵇ_) renaming (_+_ to _+ℚ_; _*_ to _*ℚ_)
open import Data.Sum as Sum using (_⊎_)
open import Data.Unit using (⊤; tt)
open import Function using (_⇔_)
open import Relation.Binary using (REL)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym; cong₂)

open import MiniVehicle.Language.Syntax.Restriction
open import MiniVehicle.Language.Interpretation
open import Util


------------------------------------------------------------------------------
-- Quantifiers

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

data QuantRel {A B : Set} (R : REL A B 0ℓ) : REL (Quant A) (Quant B) 0ℓ where
  return : ∀ {a b} → R a b → QuantRel R (return a) (return b)
  _and_ : ∀ {a b c d} → QuantRel R a b → QuantRel R c d → QuantRel R (a and c) (b and d)
  _or_ : ∀ {a b c d} → QuantRel R a b → QuantRel R c d → QuantRel R (a or c) (b or d)
  ex : ∀ {f g} → (∀ q → QuantRel R (f q) (g q)) → QuantRel R (ex f) (ex g)

eval-QuantRel : ∀ {A B} {x : Quant A} {y : Quant B} {f : A → Set} {g : B → Set} →
               QuantRel (λ a b → (f a) ⇔ (g b)) x y →
               (eval-Quant x f) ⇔ (eval-Quant y g)
eval-QuantRel {x = return _} {return _} (return Rxy) = Rxy
eval-QuantRel {x = _ and _} {_ and _} (Rxy₁ and Rxy₂) = eval-QuantRel Rxy₁ ×-⇔ eval-QuantRel Rxy₂
eval-QuantRel {x = _ or _} {_ or _} (Rxy₁ or Rxy₂) = eval-QuantRel Rxy₁ ⊎-⇔ eval-QuantRel Rxy₂
eval-QuantRel {x = ex _} {ex _} (ex Rxy) = Σ-⇔ (λ {x} → eval-QuantRel (Rxy x))

------------------------------------------------------------------------------
-- Standard model

module _ (extFunc : ℚ → ℚ) where
  open Model

  ℳ : Model defaultRestriction (suc 0ℓ) 0ℓ
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
  ℳ .⟦Bool⟧ U = 𝔹
  ℳ .⟦Bool⟧ Ex = Quant 𝔹
  ℳ .⟦not⟧ (U , x) = not x
  ℳ .⟦and⟧ (U-U , x , y) = x ∧ y
  ℳ .⟦and⟧ (U-Ex , x , y) = (return x) and y
  ℳ .⟦and⟧ (Ex-U , x , y) = x and (return y)
  ℳ .⟦and⟧ (Ex-Ex , x , y) = x and y
  ℳ .⟦or⟧ (U-U , x , y) = x ∨ y
  ℳ .⟦or⟧ (U-Ex , x , y) = (return x) or y
  ℳ .⟦or⟧ (Ex-U , x , y) = x or (return y)
  ℳ .⟦or⟧ (Ex-Ex , x , y) = x or y
  ℳ .⟦≤⟧ (U , q₁ , q₂) = q₁ ≤ᵇ q₂
  ℳ .⟦<⟧ (U , q₁ , q₂) = q₁ <ᵇ q₂
  ℳ .⟦if⟧ ((tr , fa) , (U , true)) = tr
  ℳ .⟦if⟧ ((tr , fa) , (U , false)) = fa
  ℳ .⟦Index⟧ i = Fin i
  ℳ .⟦idx⟧ _ i _  = i
  ℳ .⟦∃⟧ (U , f) = ex (λ q → return (f q))
  ℳ .⟦∃⟧ (Ex , f) = ex f
