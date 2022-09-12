{-# OPTIONS --postfix-projections #-}

module Normalisation where

open import Level using (Lift; lift; lower; suc; 0ℓ)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.Rational using (ℚ; 1ℚ)
open import Data.Unit using (⊤; tt)

open import MiniVehicle hiding (_⇒ᵣ_; under)
open import NormalisedExpr
open import Interpretation

record Syn : Set₁ where
  field
    Carrier : LinVarCtxt → Set
    rename  : ∀ {Δ Δ'} → (Δ ⇒ᵣ Δ') → Carrier Δ' → Carrier Δ
open Syn public

K : Set → Syn
K A .Carrier Δ = A
K A .rename ρ a = a

record _==>_ (X Y : Syn) : Set where
  field
    mor : ∀ {Δ} → X .Carrier Δ → Y .Carrier Δ
open _==>_ public

⟦Bool⟧ : BoolKind → Syn
⟦Bool⟧ query .Carrier = Query
⟦Bool⟧ query .rename = rename-Query
⟦Bool⟧ constraint .Carrier = ConstraintExp
⟦Bool⟧ constraint .rename = rename-ConstraintExp

⟦Num⟧ : Linearity → Syn
⟦Num⟧ const = K ℚ
⟦Num⟧ linear .Carrier = LinExp
⟦Num⟧ linear .rename = rename-LinExp

data LetLift (A : LinVarCtxt → Set) : LinVarCtxt → Set where
  return     : ∀ {Δ} → A Δ → LetLift A Δ
  if         : ∀ {Δ} → ConstraintExp Δ → LetLift A Δ → LetLift A Δ → LetLift A Δ
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
  if (rename-ConstraintExp ρ p) (rename-lift rA ρ k₁) (rename-lift rA ρ k₂)
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

⟦∀⟧ : (ℕ → Syn) → Syn
⟦∀⟧ A .Carrier Δ = (n : ℕ) → A n .Carrier Δ
⟦∀⟧ A .rename ρ f n = A n .rename ρ (f n)

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

------------------------------------------------------------------------------
⟦return⟧ : ∀ {X} → X ==> LiftM X
⟦return⟧ .mor = return

extend : ∀ {X Y Z} → ((X ⟦×⟧ Y) ==> LiftM Z) → (X ⟦×⟧ LiftM Y) ==> LiftM Z
extend {X} f .mor (x , ly) =
  bind-let ly (λ Δ' ρ y → f .mor (X .rename ρ x , y))

------------------------------------------------------------------------------
⟦add⟧ : (⟦Num⟧ linear ⟦×⟧ ⟦Num⟧ linear) ==> ⟦Num⟧ linear
⟦add⟧ .mor (x , y) = x `+` y

⟦mul⟧ : (⟦Num⟧ const ⟦×⟧ ⟦Num⟧ linear) ==> ⟦Num⟧ linear
⟦mul⟧ .mor (x , y) = x ⊛ y

⟦≤⟧ : (⟦Num⟧ linear ⟦×⟧ ⟦Num⟧ linear) ==> ⟦Bool⟧ constraint
⟦≤⟧ .mor (x , y) = x `≤` y

⟦and⟧ : (⟦Bool⟧ constraint ⟦×⟧ ⟦Bool⟧ constraint) ==> ⟦Bool⟧ constraint
⟦and⟧ .mor (x , y) = x and y

⟦or⟧ : (⟦Bool⟧ constraint ⟦×⟧ ⟦Bool⟧ constraint) ==> ⟦Bool⟧ constraint
⟦or⟧ .mor (x , y) = x or y

⟦num⟧ : ∀ {X} → ℚ → X ==> ⟦Num⟧ const
⟦num⟧ q .mor x = q

⟦const⟧ : ⟦Num⟧ const ==> ⟦Num⟧ linear
⟦const⟧ .mor x = const x

⟦not⟧ : ⟦Bool⟧ constraint ==> ⟦Bool⟧ constraint
⟦not⟧ .mor = negate

⟦eval⟧ : ∀ {X Y} → ((X ⟦⇒⟧ Y) ⟦×⟧ X) ==> Y
⟦eval⟧ .mor {Δ} (f , x) = f Δ (λ v → v) x

⟦extFunc⟧ : ⟦Num⟧ linear ==> LiftM (⟦Num⟧ linear)
⟦extFunc⟧ .mor exp =
  let-linexp exp (let-funexp {- f -} zero (return (var 1ℚ zero)))

⟦Λ⟧ : ∀ {X Y Z} → ((X ⟦×⟧ Y) ==> Z) → (X ==> (Y ⟦⇒⟧ Z))
⟦Λ⟧ {X} f .mor x = λ Δ' ρ y → f .mor (X .rename ρ x , y)

⟦∀-intro⟧ : ∀ {X A} → (∀ n → X ==> A n) → X ==> ⟦∀⟧ A
⟦∀-intro⟧ f .mor x n = f n .mor x

⟦∀-elim⟧ : ∀ {A} n → ⟦∀⟧ A ==> A n
⟦∀-elim⟧ n .mor f = f n

⟦if⟧ : ∀ {X} → ((LiftM X ⟦×⟧ LiftM X) ⟦×⟧ ⟦Bool⟧ constraint) ==> LiftM X
⟦if⟧ .mor ((tr , fa) , ϕ)= if ϕ tr fa

⟦Index⟧ : ℕ → Syn
⟦Index⟧ n = K (Fin n)

ℳ : Model (suc 0ℓ) 0ℓ
ℳ .Model.⟦Type⟧ = Syn
ℳ .Model._==>_ = _==>_
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
ℳ .Model.⟦extend⟧ = extend
ℳ .Model.⟦Num⟧ = ⟦Num⟧
ℳ .Model.⟦add⟧ = ⟦add⟧
ℳ .Model.⟦mul⟧ = ⟦mul⟧
ℳ .Model.⟦num⟧ = ⟦num⟧
ℳ .Model.⟦const⟧ = ⟦const⟧
ℳ .Model.⟦extFunc⟧ = ⟦extFunc⟧
ℳ .Model.⟦Bool⟧ = ⟦Bool⟧
ℳ .Model.⟦not⟧ = ⟦not⟧
ℳ .Model.⟦and⟧ = ⟦and⟧
ℳ .Model.⟦or⟧ = ⟦or⟧
ℳ .Model.⟦≤⟧ = ⟦≤⟧
ℳ .Model.⟦if⟧ = ⟦if⟧
ℳ .Model.⟦Index⟧ = ⟦Index⟧
ℳ .Model.⟦idx⟧ n i .mor _ = i
ℳ .Model.⟦constraint⟧ .mor = constraint
ℳ .Model.⟦∃⟧ .mor {Δ} f = ex (compile (f (Δ ,∙) succ (var 1ℚ zero)))
