module MiniVehicle.Language.Model where

open import Level using (suc; _⊔_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Rational using (ℚ)
open import MiniVehicle.Language.Syntax.Restriction

record Model (R : Restriction) ℓ m : Set (suc ℓ ⊔ suc m) where
  open Restriction R
  field
    ⟦Type⟧ : Set ℓ
    _==>_ : ⟦Type⟧ → ⟦Type⟧ → Set m

    ⟦id⟧  : ∀ {X} → X ==> X
    _∘_   : ∀ {X Y Z} → Y ==> Z → X ==> Y → X ==> Z

    -- Sets as interpretations of types
    Flat : Set → ⟦Type⟧
    elem : ∀ {A X} → A → X ==> Flat A
    Flat-map : ∀ {A B} → (A → B) → Flat A ==> Flat B

    -- finite products
    _⟦×⟧_      : ⟦Type⟧ → ⟦Type⟧ → ⟦Type⟧
    ⟦⊤⟧        : ⟦Type⟧
    ⟦terminal⟧ : ∀ {X} → X ==> ⟦⊤⟧
    ⟦proj₁⟧    : ∀ {X Y} → (X ⟦×⟧ Y) ==> X
    ⟦proj₂⟧    : ∀ {X Y} → (X ⟦×⟧ Y) ==> Y
    ⟨_,_⟩      : ∀ {X Y Z} → (X ==> Y) → (X ==> Z) → (X ==> (Y ⟦×⟧ Z))

    -- closure
    _⟦⇒⟧_ : ⟦Type⟧ → ⟦Type⟧ → ⟦Type⟧
    ⟦Λ⟧    : ∀ {X Y Z} → ((X ⟦×⟧ Y) ==> Z) → (X ==> (Y ⟦⇒⟧ Z))
    ⟦eval⟧ : ∀ {X Y} → ((X ⟦⇒⟧ Y) ⟦×⟧ X) ==> Y

    -- Universal types
    ⟦∀⟧       : ∀ {I : Set} → (I → ⟦Type⟧) → ⟦Type⟧
    ⟦∀-intro⟧ : ∀ {I X A} → (∀ (n : I) → X ==> A n) → X ==> ⟦∀⟧ A
    ⟦∀-elim⟧  : ∀ {I A} (n : I) → ⟦∀⟧ A ==> A n

    -- Monad
    Mon      : ⟦Type⟧ → ⟦Type⟧
    ⟦return⟧ : ∀ {X} → X ==> Mon X
    ⟦extend⟧ : ∀ {X Y Z} → ((X ⟦×⟧ Y) ==> Mon Z) → (X ⟦×⟧ Mon Y) ==> Mon Z

    -- Actual stuff
    ⟦Bool⟧ : BoolRestriction → ⟦Type⟧
    ⟦Num⟧  : NumRestriction → ⟦Type⟧

    ⟦not⟧ : ∀ {b₁ b₂} → (Flat (NotRestriction b₁ b₂) ⟦×⟧ ⟦Bool⟧ b₁) ==> ⟦Bool⟧ b₂
    ⟦and⟧ : ∀ {b₁ b₂ b₃} → (Flat (AndRestriction b₁ b₂ b₃) ⟦×⟧ (⟦Bool⟧ b₁ ⟦×⟧ ⟦Bool⟧ b₂)) ==> ⟦Bool⟧ b₃
    ⟦or⟧ : ∀ {b₁ b₂ b₃} → (Flat (OrRestriction b₁ b₂ b₃) ⟦×⟧ (⟦Bool⟧ b₁ ⟦×⟧ ⟦Bool⟧ b₂)) ==> ⟦Bool⟧ b₃

    -- TODO: can we move the restriction to the front like the rest?
    ⟦if⟧ : ∀ {X b} → ((Mon X ⟦×⟧ Mon X) ⟦×⟧ (Flat (IfRestriction b) ⟦×⟧ (⟦Bool⟧ b))) ==> Mon X

    ⟦∃⟧    : ∀ {l b₁ b₂} → (Flat (QuantRestriction l b₁ b₂) ⟦×⟧ (⟦Num⟧ l ⟦⇒⟧ Mon (⟦Bool⟧ b₁))) ==> ⟦Bool⟧ b₂

  ⟦Index⟧ : ℕ → ⟦Type⟧
  ⟦Index⟧ n = Flat (Fin n)

  ⟦Vec⟧ : ℕ → ⟦Type⟧ → ⟦Type⟧
  ⟦Vec⟧ n X = ⟦Index⟧ n ⟦⇒⟧ (Mon X)

  field
    ⟦add⟧     : ∀ {l₁ l₂ l₃} → (Flat (AddRestriction l₁ l₂ l₃) ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Num⟧ l₃
    ⟦mul⟧     : ∀ {l₁ l₂ l₃} → (Flat (MulRestriction l₁ l₂ l₃) ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Num⟧ l₃
    ⟦const⟧   : ∀ {l₁} → ℚ → (Flat (NumConstRestriction l₁)) ==> ⟦Num⟧ l₁
    ⟦extFunc⟧ : ∀ {l₁ l₂} → (Flat (FuncRestriction l₁ l₂) ⟦×⟧ ⟦Num⟧ l₁) ==> Mon (⟦Num⟧ l₂)
    ⟦≤⟧       : ∀ {l₁ l₂ b₃} → (Flat (CompRestriction l₁ l₂ b₃) ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Bool⟧ b₃
    ⟦<⟧       : ∀ {l₁ l₂ b₃} → (Flat (CompRestriction l₁ l₂ b₃) ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Bool⟧ b₃
