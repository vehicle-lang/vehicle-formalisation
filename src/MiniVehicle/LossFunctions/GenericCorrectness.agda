
open import Data.Rational using (ℚ; _+_; _*_; _≤ᵇ_; _≟_; 1ℚ)
open import MiniVehicle.LossFunctions.GenericDifferentiableLogic

module MiniVehicle.LossFunctions.GenericCorrectness
  (extFunc : ℚ → ℚ) (dl : DifferentiableLogic) (dl-valid : ValidDifferentiableLogic dl) where

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
open import MiniVehicle.Language.Interpretation
open import EquiInhabited

import MiniVehicle.LossFunctions.GenericCompilation as N
import MiniVehicle.Language.Syntax N.lossRestriction as MiniVehicle
import MiniVehicle.Language.StandardSemantics as S

open DifferentiableLogic dl
open ValidDifferentiableLogic dl-valid

------------------------------------------------------------------------------
-- Our category of related interpretations

module 𝒩 = Model (N.ℳ extFunc dl)
module 𝒮 = Model (S.ℳ extFunc)

record WRel : Set (suc 0ℓ) where
  field
    Left  : 𝒮.⟦Type⟧
    Right : 𝒩.⟦Type⟧
    rel   : Left → Right → Set
open WRel

infixr 20 _==>_
record _==>_ (X Y : WRel) : Set where
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

Flat : Set → WRel
Flat X .Left = X
Flat X .Right = X
Flat X .rel = _≡_

elem : ∀ {A X} → A → X ==> Flat A
elem a .left = 𝒮.elem a
elem a .right = 𝒩.elem a
elem a .rel-mor _ _ _ = refl

------------------------------------------------------------------------------
-- Products and terminal object

⟦⊤⟧ : WRel
⟦⊤⟧ .Left = ⊤
⟦⊤⟧ .Right = 𝒩.⟦⊤⟧
⟦⊤⟧ .rel tt tt = ⊤

⟦terminal⟧ : ∀ {X} → X ==> ⟦⊤⟧
⟦terminal⟧ .left = 𝒮.⟦terminal⟧
⟦terminal⟧ .right = 𝒩.⟦terminal⟧
⟦terminal⟧ .rel-mor _ _ _ = tt

infixr 2 _⟦×⟧_
_⟦×⟧_ : WRel → WRel → WRel
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

_⟦⇒⟧_ : WRel → WRel → WRel
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

⟦∀⟧ : ∀ {I : Set} → (I → WRel) → WRel
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
-- Index

⟦Index⟧ : ℕ → WRel
⟦Index⟧ n .Left = 𝒮.⟦Index⟧ n
⟦Index⟧ n .Right = 𝒩.⟦Index⟧ n
⟦Index⟧ X .rel x y = x ≡ y

⟦idx⟧ : (n : ℕ)(i : Fin n) → ∀ {X} → X ==> ⟦Index⟧ n
⟦idx⟧ n i .left = 𝒮.⟦idx⟧ n i
⟦idx⟧ n i .right = 𝒩.⟦idx⟧ n i
⟦idx⟧ n i .rel-mor _ _ _ = refl

------------------------------------------------------------------------------
-- Numbers, and linear expressions

⟦Num⟧ : ⊤ → WRel
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

⟦Bool⟧ : PolarityVal → WRel
⟦Bool⟧ p .Left = 𝒮.⟦Bool⟧ p
⟦Bool⟧ p .Right = 𝒩.⟦Bool⟧ p
⟦Bool⟧ U .rel = _⇿_
⟦Bool⟧ Ex .rel = S.QuantRel _⇿_

⟦≤⟧ : ∀ {l₁ l₂ l₃} → (Flat (ConstPolRel l₃) ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Bool⟧ l₃
⟦≤⟧ .left = 𝒮.⟦≤⟧
⟦≤⟧ .right = 𝒩.⟦≤⟧
⟦≤⟧ .rel-mor (U , x , y) (_ , p , q) (refl , refl , refl) = ⟪≤⟫-⇿ p q

⟦<⟧ : ∀ {l₁ l₂ l₃} → (Flat (ConstPolRel l₃) ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Bool⟧ l₃
⟦<⟧ .left = 𝒮.⟦<⟧
⟦<⟧ .right = 𝒩.⟦<⟧
⟦<⟧ .rel-mor (U , x , y) (_ , p , q) (refl , refl , refl) = ⟪<⟫-⇿ p q

⟦and⟧ : ∀ {l₁ l₂ l₃} → (Flat (MaxPolRel l₁ l₂ l₃) ⟦×⟧ (⟦Bool⟧ l₁ ⟦×⟧ ⟦Bool⟧ l₂)) ==> ⟦Bool⟧ l₃
⟦and⟧ .left = 𝒮.⟦and⟧
⟦and⟧ .right = 𝒩.⟦and⟧
⟦and⟧ .rel-mor (U-U , a , b) (U-U , p , q) (_ , a⇿p , b⇿q) = begin
  True (a ∧ b)        ⇔˘⟨ True-∧-⇔ ⟩
  True a × True b     ⇔⟨ a⇿p ×-⇔ b⇿q ⟩
  Truish p × Truish q ⇔⟨ ⟪and⟫-⇿ p q ⟩
  Truish (p ⟪and⟫ q)  ∎
  where open ⇔-Reasoning
⟦and⟧ .rel-mor (U-Ex , _) (U-Ex , _) (_ , x₁₂ , y₁₂) = S.return x₁₂ S.and y₁₂
⟦and⟧ .rel-mor (Ex-U , _) (Ex-U , _) (_ , x₁₂ , y₁₂) = x₁₂ S.and S.return y₁₂
⟦and⟧ .rel-mor (Ex-Ex , _) (Ex-Ex , _) (_ ,  x₁₂ , y₁₂) = x₁₂ S.and y₁₂

⟦or⟧ : ∀ {l₁ l₂ l₃} →
          (Flat (MaxPolRel l₁ l₂ l₃) ⟦×⟧
            (⟦Bool⟧ l₁ ⟦×⟧ ⟦Bool⟧ l₂)) ==> ⟦Bool⟧ l₃
⟦or⟧ .left = 𝒮.⟦or⟧
⟦or⟧ .right = 𝒩.⟦or⟧
⟦or⟧ .rel-mor (U-U , a , b) (U-U , p , q) (_ , a⇿p , b⇿q) = begin
  True (a ∨ b)          ⇔˘⟨ True-∨-⇔ ⟩
  (True a ⊎ True b)     ⇔⟨ a⇿p ⊎-⇔ b⇿q ⟩
  (Truish p ⊎ Truish q) ⇔⟨ ⟪or⟫-⇿ p q ⟩
  Truish (p ⟪or⟫ q)     ∎
  where open ⇔-Reasoning
⟦or⟧ .rel-mor (U-Ex , _) (U-Ex , _) (_ , x₁₂ , y₁₂) = S.return x₁₂ S.or y₁₂
⟦or⟧ .rel-mor (Ex-U , _) (Ex-U , _) (_ , x₁₂ , y₁₂) = x₁₂ S.or S.return y₁₂
⟦or⟧ .rel-mor (Ex-Ex , _) (Ex-Ex , _) (_ , x₁₂ , y₁₂) = x₁₂ S.or y₁₂

⟦not⟧ : ∀ {p₁ p₂} → (Flat (NegPolRel p₁ p₂) ⟦×⟧ ⟦Bool⟧ p₁) ==> ⟦Bool⟧ p₂
⟦not⟧ .left = 𝒮.⟦not⟧
⟦not⟧ .right = 𝒩.⟦not⟧
⟦not⟧ .rel-mor (U , a) (_ , p) (refl , a⇿p) =
  ¬?-⇔ (True? (not a)) (Truish? (⟪not⟫ p)) $
  begin
    ¬ (True (not a))       ⇔⟨ True-not-⇔ ⟩
    True (not (not a))     ≡⟨ cong True (not-involutive a) ⟩
    True a                 ⇔⟨ a⇿p ⟩
    Truish p               ⇔⟨ ⟪not⟫-⇿ p ⟩
    (¬ (Truish (⟪not⟫ p))) ∎
    where open ⇔-Reasoning

------------------------------------------------------------------------------
-- Monad (identity)

Mon : WRel → WRel
Mon X .Left = 𝒮.Mon (X .Left)
Mon X .Right = 𝒩.Mon (X .Right)
Mon X .rel = X .rel

⟦return⟧ : ∀ {X} → X ==> Mon X
⟦return⟧ .left = 𝒮.⟦return⟧
⟦return⟧ .right = 𝒩.⟦return⟧
⟦return⟧ .rel-mor x₁ x₂ r-x₁x₂ = r-x₁x₂

⟦extFunc⟧ : ∀ {l₁ l₂} → (Flat ⊤ ⟦×⟧ ⟦Num⟧ l₁) ==> Mon (⟦Num⟧ l₂)
⟦extFunc⟧ .left = 𝒮.⟦extFunc⟧
⟦extFunc⟧ .right = 𝒩.⟦extFunc⟧
⟦extFunc⟧ .rel-mor (_ , x₁) (_ , x₂) (_ , r-x₁x₂) = cong extFunc r-x₁x₂

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
ℳ .Model.⟦Type⟧ = WRel
ℳ .Model._==>_ = _==>_
ℳ .Model.Flat = Flat
ℳ .Model.elem = elem
ℳ .Model.⟦id⟧ = ⟦id⟧
ℳ .Model._∘_ = _∘_
ℳ .Model._⟦×⟧_ = _⟦×⟧_
ℳ .Model.⟦⊤⟧ = ⟦⊤⟧
ℳ .Model.⟦terminal⟧ = ⟦terminal⟧
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
ℳ .Model.⟦extFunc⟧ = ⟦extFunc⟧
ℳ .Model.⟦Bool⟧ = ⟦Bool⟧
ℳ .Model.⟦not⟧ = ⟦not⟧
ℳ .Model.⟦and⟧ = ⟦and⟧
ℳ .Model.⟦or⟧ = ⟦or⟧
ℳ .Model.⟦≤⟧ = ⟦≤⟧
ℳ .Model.⟦<⟧ = ⟦<⟧
ℳ .Model.⟦if⟧ {X} {b} = ⟦if⟧ {X} {b}
ℳ .Model.⟦Index⟧ = ⟦Index⟧
ℳ .Model.⟦idx⟧ = ⟦idx⟧
ℳ .Model.⟦∃⟧ = ⟦∃⟧

open MiniVehicle hiding (_⇒ᵣ_; under)

module ℐ = Interpret N.lossRestriction ℳ

------------------------------------------------------------------------------
-- Propositional compilation

standardProp : ε / ε ⊢ Bool (BoolRes U) → 𝔹
standardProp t = ℐ.⟦ t ⟧tm (lift tt) .left tt

lossFunctionProp : ε / ε ⊢ Bool (BoolRes U) → ⟪Bool⟫
lossFunctionProp t = ℐ.⟦ t ⟧tm (lift tt) .right tt

prop-correctness : (t : ε / ε ⊢ Bool (BoolRes U)) → standardProp t ⇿ lossFunctionProp t
prop-correctness t = ℐ.⟦ t ⟧tm (lift tt) .rel-mor tt tt tt

------------------------------------------------------------------------------
-- Quantified compilation

standard : ε / ε ⊢ Bool (BoolRes Ex) → Set
standard t = S.eval-Quant (ℐ.⟦_⟧tm t (lift tt) .left tt) True

lossFunction : ε / ε ⊢ Bool (BoolRes Ex) → Set
lossFunction t = S.eval-Quant (ℐ.⟦ t ⟧tm (lift tt) .right tt) Truish

full-correctness : (t : ε / ε ⊢ Bool (BoolRes Ex)) → standard t ⇔ lossFunction t
full-correctness t = S.eval-QuantRel (ℐ.⟦ t ⟧tm (lift tt) .rel-mor tt tt tt)
