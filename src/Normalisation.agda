{-# OPTIONS --postfix-projections #-}

module Normalisation where

open import Level using (Lift; lift; lower; suc; 0ℓ)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.Rational using (ℚ; 1ℚ; _+_; _*_)
open import Data.Unit using (⊤; tt)

open import MiniVehicle.Qualifiers
open import NormalisedExpr
open import Interpretation

record Syn : Set₁ where
  field
    Carrier : LinVarCtxt → Set
    rename  : Renameable Carrier
open Syn public

K : Set → Syn
K A .Carrier Δ = A
K A .rename ρ a = a

record _==>_ (X Y : Syn) : Set where
  field
    mor : ∀ {Δ} → X .Carrier Δ → Y .Carrier Δ
open _==>_ public

Flat : Set → Syn
Flat = K

⟦Bool⟧ : LinearityVal → PolarityVal → Syn
⟦Bool⟧ _ Ex .Carrier = Query
⟦Bool⟧ _ Ex .rename = rename-Query
⟦Bool⟧ _ U .Carrier = Constraint
⟦Bool⟧ _ U .rename = rename-Constraint

⟦Num⟧ : LinearityVal → Syn
⟦Num⟧ const = K ℚ
⟦Num⟧ linear .Carrier = LinExp
⟦Num⟧ linear .rename = rename-LinExp
⟦Num⟧ nonlinear = K ⊤

data LetLift (A : LinVarCtxt → Set) : LinVarCtxt → Set where
  return     : ∀ {Δ} → A Δ → LetLift A Δ
  if         : ∀ {Δ} → Constraint Δ → LetLift A Δ → LetLift A Δ → LetLift A Δ
  let-linexp : ∀ {Δ} → LinExp Δ → LetLift A (Δ ,∙) → LetLift A Δ
  let-funexp : ∀ {Δ} → {- fsymb → -} Var Δ → LetLift A (Δ ,∙) → LetLift A Δ

-- expand a Query within lets and ifs into a Query
compile : ∀ {Δ} → LetLift Query Δ → Query Δ
compile (return x)       = x
compile (if ϕ tr fa)     = ((constraint ϕ) and (compile tr)) or (constraint (negate ϕ) and (compile fa))
compile (let-linexp e k) = ex ((constraint ((var 1ℚ zero) `=` rename-LinExp succ e)) and compile k)
compile (let-funexp x k) = ex ((constraint (zero `=`f (succ x))) and (compile k))

rename-lift : ∀ {A} → Renameable A → Renameable (LetLift A)
rename-lift rA ρ (return x) =
  return (rA ρ x)
rename-lift rA ρ (if p k₁ k₂) =
  if (rename-Constraint ρ p) (rename-lift rA ρ k₁) (rename-lift rA ρ k₂)
rename-lift rA ρ (let-linexp e k) =
  let-linexp (rename-LinExp ρ e) (rename-lift rA (under ρ) k)
rename-lift rA ρ (let-funexp v k) =
  let-funexp (ρ v) (rename-lift rA (under ρ) k)

bind-let : ∀ {Δ A B} → LetLift A Δ → (A ⇒ₖ LetLift B) Δ → LetLift B Δ
bind-let (return x)       f = f _ (λ x → x) x
bind-let (if e kt kf)     f = if e (bind-let kt f) (bind-let kf f)
bind-let (let-linexp e k) f = let-linexp e (bind-let k (rename-⇒ₖ succ f))
bind-let (let-funexp x k) f = let-funexp x (bind-let k (rename-⇒ₖ succ f))

LiftM : Syn → Syn
LiftM A .Carrier = LetLift (A .Carrier)
LiftM A .rename = rename-lift (A .rename)

_⟦⇒⟧_ : Syn → Syn → Syn
(X ⟦⇒⟧ Y) .Carrier = X .Carrier ⇒ₖ Y .Carrier
(X ⟦⇒⟧ Y) .rename = rename-⇒ₖ

_⟦×⟧_ : Syn → Syn → Syn
(A ⟦×⟧ B) .Carrier Δ = A .Carrier Δ × B .Carrier Δ
(A ⟦×⟧ B) .rename ρ (a , b) = A .rename ρ a , B .rename ρ b

⟦⊤⟧ : Syn
⟦⊤⟧ = K ⊤

------------------------------------------------------------------------------
⟨_,_⟩ : ∀ {X Y Z} → (X ==> Y) → (X ==> Z) → (X ==> (Y ⟦×⟧ Z))
⟨ f , g ⟩ .mor x = f .mor x , g .mor x

⟦proj₁⟧ : ∀ {X Y} → (X ⟦×⟧ Y) ==> X
⟦proj₁⟧ .mor (x , y) = x

⟦proj₂⟧ : ∀ {X Y} → (X ⟦×⟧ Y) ==> Y
⟦proj₂⟧ .mor (x , y) = y

⟦terminal⟧ : ∀ {X} → X ==> ⟦⊤⟧
⟦terminal⟧ .mor x = tt

⟦id⟧ : ∀ {X} → X ==> X
⟦id⟧ .mor x = x
_∘S_ : ∀ {X Y Z} → (Y ==> Z) → (X ==> Y) → (X ==> Z)
(f ∘S g) .mor x = f .mor (g .mor x)

⟦eval⟧ : ∀ {X Y} → ((X ⟦⇒⟧ Y) ⟦×⟧ X) ==> Y
⟦eval⟧ .mor {Δ} (f , x) = f Δ (λ v → v) x

⟦Λ⟧ : ∀ {X Y Z} → ((X ⟦×⟧ Y) ==> Z) → (X ==> (Y ⟦⇒⟧ Z))
⟦Λ⟧ {X} f .mor x = λ Δ' ρ y → f .mor (X .rename ρ x , y)

------------------------------------------------------------------------------
⟦∀⟧ : ∀ {I : Set} → (I → Syn) → Syn
⟦∀⟧ A .Carrier Δ = ∀ n → A n .Carrier Δ
⟦∀⟧ A .rename ρ f n = A n .rename ρ (f n)

⟦∀-intro⟧ : ∀ {I X A} → (∀ (n : I) → X ==> A n) → X ==> ⟦∀⟧ A
⟦∀-intro⟧ f .mor x n = f n .mor x

⟦∀-elim⟧ : ∀ {I A} (n : I) → ⟦∀⟧ A ==> A n
⟦∀-elim⟧ n .mor f = f n

------------------------------------------------------------------------------
⟦return⟧ : ∀ {X} → X ==> LiftM X
⟦return⟧ .mor = return

⟦extend⟧ : ∀ {X Y Z} → ((X ⟦×⟧ Y) ==> LiftM Z) → (X ⟦×⟧ LiftM Y) ==> LiftM Z
⟦extend⟧ {X} f .mor (x , ly) =
  bind-let ly (λ Δ' ρ y → f .mor (X .rename ρ x , y))

------------------------------------------------------------------------------
⟦add⟧ : ∀ {l₁ l₂ l₃} → (Flat (MaxLinRel l₁ l₂ l₃) ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Num⟧ l₃
⟦add⟧ .mor (const-const , x , y) = x + y
⟦add⟧ .mor (const-linear , x , y) = const x `+` y
⟦add⟧ .mor (linear-const , x , y) = x `+` const y
⟦add⟧ .mor (linear-linear , x , y) = x `+` y

⟦mul⟧ : ∀ {l₁ l₂ l₃} → (Flat (MulRel l₁ l₂ l₃) ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Num⟧ l₃
⟦mul⟧ .mor (const-const , x , y) = x * y
⟦mul⟧ .mor (const-linear , x , y) = x ⊛ y
⟦mul⟧ .mor (linear-const , x , y) = y ⊛ x

⟦≤⟧ : ∀ {l₁ l₂ l₃} → (Flat (MaxLinRel l₁ l₂ l₃) ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Bool⟧ l₃ U
⟦≤⟧ .mor (const-const ,   x , y) = const x `≤` const y
⟦≤⟧ .mor (const-linear ,  x , y) = const x `≤` y
⟦≤⟧ .mor (linear-const ,  x , y) = x `≤` const y
⟦≤⟧ .mor (linear-linear , x , y) = x `≤` y

⟦not⟧ : ∀ {l p₁ p₂} → (Flat (NegPolRel p₁ p₂) ⟦×⟧ ⟦Bool⟧ l p₁) ==> ⟦Bool⟧ l p₂
⟦not⟧ .mor (U , x) = negate x

⟦and⟧ : ∀ {l₁ l₂ l₃ p₁ p₂ p₃} →
         (Flat (MaxLinRel l₁ l₂ l₃) ⟦×⟧
          (Flat (MaxPolRel p₁ p₂ p₃) ⟦×⟧
           (⟦Bool⟧ l₁ p₁ ⟦×⟧ ⟦Bool⟧ l₂ p₂))) ==> ⟦Bool⟧ l₃ p₃
⟦and⟧ .mor (p , U-U ,   x , y) = x and y
⟦and⟧ .mor (p , U-Ex ,  x , y) = constraint x and y
⟦and⟧ .mor (p , Ex-U ,  x , y) = x and constraint y
⟦and⟧ .mor (p , Ex-Ex , x , y) = x and y

⟦or⟧ : ∀ {l₁ l₂ l₃ p₁ p₂ p₃} →
         (Flat (MaxLinRel l₁ l₂ l₃) ⟦×⟧
          (Flat (MaxPolRel p₁ p₂ p₃) ⟦×⟧
           (⟦Bool⟧ l₁ p₁ ⟦×⟧ ⟦Bool⟧ l₂ p₂))) ==> ⟦Bool⟧ l₃ p₃
⟦or⟧ .mor (p , U-U ,   x , y) = x or y
⟦or⟧ .mor (p , U-Ex ,  x , y) = constraint x or y
⟦or⟧ .mor (p , Ex-U ,  x , y) = x or constraint y
⟦or⟧ .mor (p , Ex-Ex , x , y) = x or y

⟦const⟧ : ∀ {X} → ℚ → X ==> ⟦Num⟧ const
⟦const⟧ q .mor _ = q

⟦extFunc⟧ : ⟦Num⟧ linear ==> LiftM (⟦Num⟧ linear)
⟦extFunc⟧ .mor exp =
  let-linexp exp (let-funexp {- f -} zero (return (var 1ℚ zero)))

⟦if⟧ : ∀ {X} → ((LiftM X ⟦×⟧ LiftM X) ⟦×⟧ ⟦Bool⟧ linear U) ==> LiftM X
⟦if⟧ .mor ((tr , fa) , ϕ)= if ϕ tr fa

⟦Index⟧ : ℕ → Syn
⟦Index⟧ n = K (Fin n)

⟦∃⟧ : ∀ {p₁ p₂ l} →
     (Flat (QuantifyRel p₁ p₂) ⟦×⟧ (⟦Num⟧ linear ⟦⇒⟧ LiftM (⟦Bool⟧ l p₁))) ==> ⟦Bool⟧ l p₂
⟦∃⟧ .mor {Δ} (U , f) = ex (compile (bind-let (f (Δ ,∙) succ (var 1ℚ zero))
                                     λ Δ' ρ ϕ → return (constraint ϕ)))
⟦∃⟧ .mor {Δ} (Ex , f) = ex (compile (f (Δ ,∙) succ (var 1ℚ zero)))

ℳ : Model (suc 0ℓ) 0ℓ
ℳ .Model.⟦Type⟧ = Syn
ℳ .Model._==>_ = _==>_
ℳ .Model.Flat = Flat
ℳ .Model.elem a .mor _ = a
ℳ .Model.⟦id⟧ = ⟦id⟧
ℳ .Model._∘_ = _∘S_
ℳ .Model._⟦×⟧_ = _⟦×⟧_
ℳ .Model.⟦⊤⟧ = ⟦⊤⟧
ℳ .Model.⟦terminal⟧ = ⟦terminal⟧
ℳ .Model.⟦proj₁⟧ = ⟦proj₁⟧
ℳ .Model.⟦proj₂⟧ = ⟦proj₂⟧
ℳ .Model.⟨_,_⟩ = ⟨_,_⟩
ℳ .Model._⟦⇒⟧_ = _⟦⇒⟧_
ℳ .Model.⟦Λ⟧ = ⟦Λ⟧
ℳ .Model.⟦eval⟧ = ⟦eval⟧
ℳ .Model.⟦∀⟧ = ⟦∀⟧
ℳ .Model.⟦∀-intro⟧ = ⟦∀-intro⟧
ℳ .Model.⟦∀-elim⟧ = ⟦∀-elim⟧
ℳ .Model.Mon = LiftM
ℳ .Model.⟦return⟧ = ⟦return⟧
ℳ .Model.⟦extend⟧ = ⟦extend⟧
ℳ .Model.⟦Num⟧ = ⟦Num⟧
ℳ .Model.⟦add⟧ = ⟦add⟧
ℳ .Model.⟦mul⟧ = ⟦mul⟧
ℳ .Model.⟦const⟧ = ⟦const⟧
ℳ .Model.⟦extFunc⟧ = ⟦extFunc⟧
ℳ .Model.⟦Bool⟧ = ⟦Bool⟧
ℳ .Model.⟦not⟧ {l} = ⟦not⟧ {l}
ℳ .Model.⟦and⟧ = ⟦and⟧
ℳ .Model.⟦or⟧ = ⟦or⟧
ℳ .Model.⟦≤⟧ = ⟦≤⟧
ℳ .Model.⟦if⟧ = ⟦if⟧
ℳ .Model.⟦Index⟧ = ⟦Index⟧
ℳ .Model.⟦idx⟧ n i .mor _ = i
ℳ .Model.⟦∃⟧ {l = l} = ⟦∃⟧ {l = l}

module 𝒩 = Interpret ℳ

open import MiniVehicle

normalise : ε / ε ⊢ Bool (LinearityConst linear) (PolarityConst Ex) → FlatQuery ε
normalise t = flatten (compile (𝒩.⟦ t ⟧tm (lift tt) .mor tt))
