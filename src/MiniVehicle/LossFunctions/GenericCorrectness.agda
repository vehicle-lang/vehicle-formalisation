
open import Data.Rational using (ℚ; _+_; _*_; _≤ᵇ_; _≟_; 1ℚ)
open import MiniVehicle.LossFunctions.GenericDifferentiableLogic

module MiniVehicle.LossFunctions.GenericCorrectness
  (extFunc : ℚ → ℚ) (dl : DifferentiableLogic) (dl-relation : DifferentiableLogicRelation dl) where

open import Level using (0ℓ; suc; lift)

open import Data.Bool using (not; _∧_; _∨_; true; false)
                   renaming (Bool to 𝔹; T to True; if_then_else_ to ifᵇ_then_else_)
open import Data.Bool.Properties using (not-involutive) renaming (T? to True?)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Rational as ℚ
open import Function using (_$_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Rational.Properties using (*-identityˡ; *-comm; ≤ᵇ⇒≤; ≤⇒≤ᵇ; module ≤-Reasoning)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (_⇔_; mk⇔; id)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; sym; cong₂; subst; module ≡-Reasoning)
open import Relation.Nullary using (¬_)

open import Util
open import MiniVehicle.Language.Syntax.Restriction
open import MiniVehicle.Language.Model
open import EquiInhabited

import MiniVehicle.LossFunctions.GenericCompilation as N
import MiniVehicle.Language.Syntax N.lossRestriction as MiniVehicle
import MiniVehicle.Language.StandardSemantics as S

open DifferentiableLogic dl
open DifferentiableLogicRelation dl-relation

------------------------------------------------------------------------------
-- Our category of related interpretations

module 𝒩 = Model (N.ℳ dl)
module 𝒮 = Model S.ℳ

record ⟦Type⟧ : Set (suc 0ℓ) where
  field
    Left  : 𝒮.⟦Type⟧
    Right : 𝒩.⟦Type⟧
    rel   : Left → Right → Set
open ⟦Type⟧

infixr 20 _==>_
record _==>_ (X Y : ⟦Type⟧) : Set where
  field
    left    : X .Left 𝒮.==> Y .Left
    right   : X .Right 𝒩.==> Y .Right
    rel-mor : ∀ lx rx → X .rel lx rx → Y .rel (left lx) (right rx)
open _==>_

------------------------------------------------------------------------------
-- Composition

_∘_ : ∀ {X Y Z} → (Y ==> Z) → (X ==> Y) → (X ==> Z)
(f ∘ g) .left  = f .left  𝒮.∘ g .left
(f ∘ g) .right = f .right 𝒩.∘ g .right
(f ∘ g) .rel-mor x₁ x₂ r-x₁x₂ = f .rel-mor _ _ (g .rel-mor _ _ r-x₁x₂)

⟦id⟧ : ∀ {X} → X ==> X
⟦id⟧ .left x = x
⟦id⟧ .right = 𝒩.⟦id⟧
⟦id⟧ .rel-mor x₁ x₂ r = r

------------------------------------------------------------------------------
-- Sets

Flat : Set → ⟦Type⟧
Flat X .Left = X
Flat X .Right = X
Flat X .rel = _≡_

elem : ∀ {A X} → A → X ==> Flat A
elem a .left = 𝒮.elem a
elem a .right = 𝒩.elem a
elem a .rel-mor _ _ _ = refl

Flat-map : ∀ {A B} → (A → B) → Flat A ==> Flat B
Flat-map f .left = f
Flat-map f .right = f
Flat-map f .rel-mor _ _ = cong f

------------------------------------------------------------------------------
-- Products

infixr 2 _⟦×⟧_

_⟦×⟧_ : ⟦Type⟧ → ⟦Type⟧ → ⟦Type⟧
(X ⟦×⟧ Y) .Left = X .Left 𝒮.⟦×⟧ Y .Left
(X ⟦×⟧ Y) .Right = X .Right 𝒩.⟦×⟧ Y .Right
(X ⟦×⟧ Y) .rel (x , y) (x' , y') = X .rel x x' × Y .rel y y'

⟨_,_⟩R : ∀ {X Y Z} → (X ==> Y) → (X ==> Z) → (X ==> (Y ⟦×⟧ Z))
⟨ f , g ⟩R .left = 𝒮.⟨ f .left , g .left ⟩
⟨ f , g ⟩R .right = 𝒩.⟨ f .right , g .right ⟩
⟨ f , g ⟩R .rel-mor x₁ x₂ r-x₁x₂ =
  f .rel-mor x₁ x₂ r-x₁x₂ ,
  g .rel-mor x₁ x₂ r-x₁x₂

⟦proj₁⟧ : ∀ {X Y} → (X ⟦×⟧ Y) ==> X
⟦proj₁⟧ .left = proj₁
⟦proj₁⟧ .right = 𝒩.⟦proj₁⟧
⟦proj₁⟧ .rel-mor _ _ r = r .proj₁

⟦proj₂⟧ : ∀ {X Y} → (X ⟦×⟧ Y) ==> Y
⟦proj₂⟧ .left = proj₂
⟦proj₂⟧ .right = 𝒩.⟦proj₂⟧
⟦proj₂⟧ .rel-mor _ _ r = r .proj₂

------------------------------------------------------------------------------
-- Functions and Universal Quantification

_⟦⇒⟧_ : ⟦Type⟧ → ⟦Type⟧ → ⟦Type⟧
(X ⟦⇒⟧ Y) .Left = X .Left 𝒮.⟦⇒⟧ Y .Left
(X ⟦⇒⟧ Y) .Right = X .Right 𝒩.⟦⇒⟧ Y .Right
(X ⟦⇒⟧ Y) .rel f g = ∀ x y →  X .rel x y → Y .rel (f x) (g y)

⟦Λ⟧ : ∀ {X Y Z} → ((X ⟦×⟧ Y) ==> Z) → (X ==> (Y ⟦⇒⟧ Z))
⟦Λ⟧ {X} f .left = 𝒮.⟦Λ⟧ (f .left)
⟦Λ⟧ {X} f .right = 𝒩.⟦Λ⟧ (f .right)
⟦Λ⟧ {X} f .rel-mor x₁ x₂ ρ y₁ y₂ q = f .rel-mor (x₁ , y₁) (x₂ , y₂) (ρ , q)

⟦eval⟧ : ∀ {X Y} → ((X ⟦⇒⟧ Y) ⟦×⟧ X) ==> Y
⟦eval⟧ .left = 𝒮.⟦eval⟧
⟦eval⟧ .right = 𝒩.⟦eval⟧
⟦eval⟧ .rel-mor (f₁ , x₁) (f₂ , x₂) (r-f₁f₂ , r-x₁x₂) = r-f₁f₂ x₁ x₂ r-x₁x₂

⟦∀⟧ : ∀ {I : Set} → (I → ⟦Type⟧) → ⟦Type⟧
⟦∀⟧ A .Left = 𝒮.⟦∀⟧ (λ n → A n .Left)
⟦∀⟧ A .Right = 𝒩.⟦∀⟧ (λ n → A n .Right)
⟦∀⟧ A .rel x y = ∀ n → A n .rel (x n) (y n)

⟦∀-intro⟧ : ∀ {I X A} → (∀ (n : I) → X ==> A n) → X ==> ⟦∀⟧ A
⟦∀-intro⟧ f .left = 𝒮.⟦∀-intro⟧ (λ n → f n .left)
⟦∀-intro⟧ f .right = 𝒩.⟦∀-intro⟧ (λ n → f n .right)
⟦∀-intro⟧ f .rel-mor x₁ x₂ r n = f n .rel-mor x₁ x₂ r

⟦∀-elim⟧ : ∀ {I A} (n : I) → ⟦∀⟧ A ==> A n
⟦∀-elim⟧ n .left = 𝒮.⟦∀-elim⟧ n
⟦∀-elim⟧ n .right = 𝒩.⟦∀-elim⟧ n
⟦∀-elim⟧ n .rel-mor f₁ f₂ r = r n

------------------------------------------------------------------------------
-- Numbers, and linear expressions

⟦Num⟧ : ⊤ → ⟦Type⟧
⟦Num⟧ p .Left = 𝒮.⟦Num⟧ p
⟦Num⟧ p .Right = 𝒩.⟦Num⟧ p
⟦Num⟧ p .rel = _≡_

⟦const⟧ : ∀ {l} → ℚ → Flat ⊤ ==> ⟦Num⟧ l
⟦const⟧ q .left _ = q
⟦const⟧ q .right = 𝒩.⟦const⟧ q
⟦const⟧ q .rel-mor const const _ = refl

⟦add⟧ : ∀ {l₁ l₂ l₃} →
         (Flat ⊤ ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Num⟧ l₃
⟦add⟧ .left = 𝒮.⟦add⟧
⟦add⟧ .right = 𝒩.⟦add⟧
⟦add⟧ .rel-mor _ _ (refl , x₁₂ , y₁₂) = cong₂ _+_ x₁₂ y₁₂

⟦mul⟧ : ∀ {l₁ l₂ l₃} → (Flat ⊤ ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Num⟧ l₃
⟦mul⟧ .left = 𝒮.⟦mul⟧
⟦mul⟧ .right = 𝒩.⟦mul⟧
⟦mul⟧ .rel-mor _ _ (refl , x₁₂ , y₁₂) = cong₂ _*_ x₁₂ y₁₂

------------------------------------------------------------------------------
-- Booleans and constraints

⟦Bool⟧ : PolarityVal → ⟦Type⟧
⟦Bool⟧ p .Left = 𝒮.⟦Bool⟧ p
⟦Bool⟧ p .Right = 𝒩.⟦Bool⟧ p
⟦Bool⟧ U .rel = R
⟦Bool⟧ Ex .rel = S.QuantRel R

⟦≤⟧ : ∀ {l₁ l₂ l₃} → (Flat (ConstPolRel l₃) ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Bool⟧ l₃
⟦≤⟧ .left = 𝒮.⟦≤⟧
⟦≤⟧ .right = 𝒩.⟦≤⟧
⟦≤⟧ .rel-mor (U , x , y) (_ , p , q) (refl , refl , refl) = R⟪≤⟫

⟦<⟧ : ∀ {l₁ l₂ l₃} → (Flat (ConstPolRel l₃) ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Bool⟧ l₃
⟦<⟧ .left = 𝒮.⟦<⟧
⟦<⟧ .right = 𝒩.⟦<⟧
⟦<⟧ .rel-mor (U , x , y) (_ , p , q) (refl , refl , refl) = R⟪<⟫

⟦and⟧ : ∀ {l₁ l₂ l₃} → (Flat (MaxPolRel l₁ l₂ l₃) ⟦×⟧ (⟦Bool⟧ l₁ ⟦×⟧ ⟦Bool⟧ l₂)) ==> ⟦Bool⟧ l₃
⟦and⟧ .left = 𝒮.⟦and⟧
⟦and⟧ .right = 𝒩.⟦and⟧
⟦and⟧ .rel-mor (U-U , a , b) (U-U , p , q) (_ , a⇿p , b⇿q) = R⟪and⟫ a⇿p b⇿q
⟦and⟧ .rel-mor (U-Ex , _) (U-Ex , _) (_ , x₁₂ , y₁₂) = S.return x₁₂ S.and y₁₂
⟦and⟧ .rel-mor (Ex-U , _) (Ex-U , _) (_ , x₁₂ , y₁₂) = x₁₂ S.and S.return y₁₂
⟦and⟧ .rel-mor (Ex-Ex , _) (Ex-Ex , _) (_ ,  x₁₂ , y₁₂) = x₁₂ S.and y₁₂

⟦or⟧ : ∀ {l₁ l₂ l₃} →
          (Flat (MaxPolRel l₁ l₂ l₃) ⟦×⟧
            (⟦Bool⟧ l₁ ⟦×⟧ ⟦Bool⟧ l₂)) ==> ⟦Bool⟧ l₃
⟦or⟧ .left = 𝒮.⟦or⟧
⟦or⟧ .right = 𝒩.⟦or⟧
⟦or⟧ .rel-mor (U-U , a , b) (U-U , p , q) (_ , a⇿p , b⇿q) = R⟪or⟫ a⇿p b⇿q
⟦or⟧ .rel-mor (U-Ex , _) (U-Ex , _) (_ , x₁₂ , y₁₂) = S.return x₁₂ S.or y₁₂
⟦or⟧ .rel-mor (Ex-U , _) (Ex-U , _) (_ , x₁₂ , y₁₂) = x₁₂ S.or S.return y₁₂
⟦or⟧ .rel-mor (Ex-Ex , _) (Ex-Ex , _) (_ , x₁₂ , y₁₂) = x₁₂ S.or y₁₂

⟦not⟧ : ∀ {p₁ p₂} → (Flat (NegPolRel p₁ p₂) ⟦×⟧ ⟦Bool⟧ p₁) ==> ⟦Bool⟧ p₂
⟦not⟧ .left = 𝒮.⟦not⟧
⟦not⟧ .right = 𝒩.⟦not⟧
⟦not⟧ .rel-mor (U , a) (_ , p) (refl , a⇿p) = R⟪not⟫ a⇿p

------------------------------------------------------------------------------
-- Monad (identity)

Mon : ⟦Type⟧ → ⟦Type⟧
Mon X .Left = 𝒮.Mon (X .Left)
Mon X .Right = 𝒩.Mon (X .Right)
Mon X .rel = X .rel

⟦return⟧ : ∀ {X} → X ==> Mon X
⟦return⟧ .left = 𝒮.⟦return⟧
⟦return⟧ .right = 𝒩.⟦return⟧
⟦return⟧ .rel-mor x₁ x₂ r-x₁x₂ = r-x₁x₂

extendR : ∀ {X Y Z} → ((X ⟦×⟧ Y) ==> Mon Z) → (X ⟦×⟧ Mon Y) ==> Mon Z
extendR f .left = 𝒮.⟦extend⟧ (f .left)
extendR f .right = 𝒩.⟦extend⟧ (f .right)
extendR {X} f .rel-mor p₁ p₂ p₁-p₂ = f .rel-mor p₁ p₂ p₁-p₂

⟦if⟧ : ∀ {X b} → ((Mon X ⟦×⟧ Mon X) ⟦×⟧ (Flat ⊥ ⟦×⟧ (⟦Bool⟧ b))) ==> Mon X
⟦if⟧ .left ()
⟦if⟧ .right ()
⟦if⟧ .rel-mor ()

⟦∃⟧ : ∀ {p₁ p₂ l} →
     (Flat (QuantifyRel p₁ p₂) ⟦×⟧ (⟦Num⟧ l ⟦⇒⟧ Mon (⟦Bool⟧ p₁))) ==> ⟦Bool⟧ p₂
⟦∃⟧ .left = 𝒮.⟦∃⟧
⟦∃⟧ {l = l} .right = 𝒩.⟦∃⟧ {l = l}
⟦∃⟧ {l = l} .rel-mor (U  , f₁) (U , f₂) (refl , r) = S.ex λ q → S.return (r q q refl)
⟦∃⟧ {l = l} .rel-mor (Ex , f₁) (Ex , f₂) (refl , r) = S.ex λ q → r q q refl

ℳ : Model N.lossRestriction (suc 0ℓ) 0ℓ
ℳ .Model.⟦Type⟧ = ⟦Type⟧
ℳ .Model._==>_ = _==>_
ℳ .Model.Flat = Flat
ℳ .Model.elem = elem
ℳ .Model.Flat-map = Flat-map
ℳ .Model.⟦id⟧ = ⟦id⟧
ℳ .Model._∘_ = _∘_
ℳ .Model._⟦×⟧_ = _⟦×⟧_
ℳ .Model.⟦proj₁⟧ = ⟦proj₁⟧
ℳ .Model.⟦proj₂⟧ = ⟦proj₂⟧
ℳ .Model.⟨_,_⟩ = ⟨_,_⟩R
ℳ .Model._⟦⇒⟧_ = _⟦⇒⟧_
ℳ .Model.⟦Λ⟧ = ⟦Λ⟧
ℳ .Model.⟦eval⟧ = ⟦eval⟧
ℳ .Model.⟦∀⟧ = ⟦∀⟧
ℳ .Model.⟦∀-intro⟧ = ⟦∀-intro⟧
ℳ .Model.⟦∀-elim⟧ = ⟦∀-elim⟧
ℳ .Model.Mon = Mon
ℳ .Model.⟦return⟧ = ⟦return⟧
ℳ .Model.⟦extend⟧ = extendR
ℳ .Model.⟦Num⟧ = ⟦Num⟧
ℳ .Model.⟦add⟧ = ⟦add⟧
ℳ .Model.⟦mul⟧ = ⟦mul⟧
ℳ .Model.⟦const⟧ = ⟦const⟧
ℳ .Model.⟦Bool⟧ = ⟦Bool⟧
ℳ .Model.⟦not⟧ = ⟦not⟧
ℳ .Model.⟦and⟧ = ⟦and⟧
ℳ .Model.⟦or⟧ = ⟦or⟧
ℳ .Model.⟦≤⟧ = ⟦≤⟧
ℳ .Model.⟦<⟧ = ⟦<⟧
ℳ .Model.⟦if⟧ {X} {b} = ⟦if⟧ {X} {b}
ℳ .Model.⟦∃⟧ = ⟦∃⟧

open MiniVehicle hiding (_⇒ᵣ_; under)

import MiniVehicle.Language.Interpretation N.lossRestriction ℳ as ℐ

------------------------------------------------------------------------------
-- Propositional compilation

standardProp : ε / ε ⊢ Bool (BoolRes U) → 𝔹
standardProp t = ℐ.⟦ t ⟧tm (lift tt) .left tt

lossFunctionProp : ε / ε ⊢ Bool (BoolRes U) → ⟪Bool⟫
lossFunctionProp t = ℐ.⟦ t ⟧tm (lift tt) .right tt

prop-correctness : (t : ε / ε ⊢ Bool (BoolRes U)) → R (standardProp t) (lossFunctionProp t)
prop-correctness t = ℐ.⟦ t ⟧tm (lift tt) .rel-mor tt tt refl

------------------------------------------------------------------------------
-- Quantified compilation

standard : ε / ε ⊢ Bool (BoolRes Ex) → Set
standard t = S.eval-Quant (ℐ.⟦_⟧tm t (lift tt) .left tt) True

lossFunction : ε / ε ⊢ Bool (BoolRes Ex) → Set
lossFunction t = S.eval-Quant (ℐ.⟦ t ⟧tm (lift tt) .right tt) (R true)
{-
full-correctness : (t : ε / ε ⊢ Bool (BoolRes Ex)) → standard t ⇔ lossFunction t
full-correctness t = S.eval-QuantRel (ℐ.⟦ t ⟧tm (lift tt) .rel-mor tt tt tt)
-}
