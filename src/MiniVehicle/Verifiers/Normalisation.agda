module MiniVehicle.Verifiers.Normalisation where

open import Level using (Lift; lift; lower; suc; 0ℓ)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.Rational using (ℚ; 1ℚ; _+_; _*_)
open import Data.Unit using (⊤; tt)

open import MiniVehicle.Language.Syntax.Restriction
open import MiniVehicle.Language.Model
open import MiniVehicle.Verifiers.Syntax.Restriction
open import VerifierLang.Syntax

record ⟦Type⟧ : Set₁ where
  field
    Carrier : LinVarCtxt → Set
    rename  : Renameable Carrier
open ⟦Type⟧ public

record _==>_ (X Y : ⟦Type⟧) : Set where
  field
    mor : ∀ {Δ} → X .Carrier Δ → Y .Carrier Δ
open _==>_ public

Flat : Set → ⟦Type⟧
Flat A .Carrier Δ = A
Flat A .rename ρ a = a

Flat-map : ∀ {A B} → (A → B) → Flat A ==> Flat B
Flat-map f .mor = f

⟦Bool⟧ : LinearityVal × PolarityVal → ⟦Type⟧
⟦Bool⟧ (_ , Ex) .Carrier = ExFormula
⟦Bool⟧ (_ , Ex) .rename = rename-ExFormula
⟦Bool⟧ (_ , U) .Carrier = Constraint
⟦Bool⟧ (_ , U) .rename = rename-Constraint

⟦Num⟧ : LinearityVal → ⟦Type⟧
⟦Num⟧ const = Flat ℚ
⟦Num⟧ linear .Carrier = LinExp
⟦Num⟧ linear .rename = rename-LinExp
⟦Num⟧ nonlinear = Flat ⊤

_⟦⇒⟧_ : ⟦Type⟧ → ⟦Type⟧ → ⟦Type⟧
(X ⟦⇒⟧ Y) .Carrier = X .Carrier ⇒ₖ Y .Carrier
(X ⟦⇒⟧ Y) .rename = rename-⇒ₖ

_⟦×⟧_ : ⟦Type⟧ → ⟦Type⟧ → ⟦Type⟧
(A ⟦×⟧ B) .Carrier Δ = A .Carrier Δ × B .Carrier Δ
(A ⟦×⟧ B) .rename ρ (a , b) = A .rename ρ a , B .rename ρ b

⟦⊤⟧ : ⟦Type⟧
⟦⊤⟧ = Flat ⊤

data LetLift (A : LinVarCtxt → Set) : LinVarCtxt → Set where
  return     : ∀ {Δ} → A Δ → LetLift A Δ
  if         : ∀ {Δ} → Constraint Δ → LetLift A Δ → LetLift A Δ → LetLift A Δ
  let-linexp : ∀ {Δ} → LinExp Δ → LetLift A (Δ ,∙) → LetLift A Δ
  let-funexp : ∀ {Δ} → {- fsymb → -} Var Δ → LetLift A (Δ ,∙) → LetLift A Δ

-- expand a ExFormula within lets and ifs into a ExFormula
compile : ∀ {Δ} → LetLift ExFormula Δ → ExFormula Δ
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

LiftM : ⟦Type⟧ → ⟦Type⟧
LiftM A .Carrier = LetLift (A .Carrier)
LiftM A .rename = rename-lift (A .rename)

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
⟦∀⟧ : ∀ {I : Set} → (I → ⟦Type⟧) → ⟦Type⟧
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

⟦mul⟧ : ∀ {l₁ l₂ l₃} → (Flat (MulLinRel l₁ l₂ l₃) ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Num⟧ l₃
⟦mul⟧ .mor (const-const , x , y) = x * y
⟦mul⟧ .mor (const-linear , x , y) = x ⊛ y
⟦mul⟧ .mor (linear-const , x , y) = y ⊛ x

⟦≤⟧ : ∀ {l₁ l₂ l₃} → (Flat (CompRes l₁ l₂ l₃) ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Bool⟧ l₃
⟦≤⟧ .mor (compRes const-const ,   x , y) = const x `≤` const y
⟦≤⟧ .mor (compRes const-linear ,  x , y) = const x `≤` y
⟦≤⟧ .mor (compRes linear-const ,  x , y) = x `≤` const y
⟦≤⟧ .mor (compRes linear-linear , x , y) = x `≤` y

⟦<⟧ : ∀ {l₁ l₂ l₃} → (Flat (CompRes l₁ l₂ l₃) ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Bool⟧ l₃
⟦<⟧ .mor (compRes const-const ,   x , y) = const x `<` const y
⟦<⟧ .mor (compRes const-linear ,  x , y) = const x `<` y
⟦<⟧ .mor (compRes linear-const ,  x , y) = x `<` const y
⟦<⟧ .mor (compRes linear-linear , x , y) = x `<` y

⟦not⟧ : ∀ {p₁ p₂} → (Flat (NotRes p₁ p₂) ⟦×⟧ ⟦Bool⟧ p₁) ==> ⟦Bool⟧ p₂
⟦not⟧ .mor (notRes U , x) = negate x

⟦and⟧ : ∀ {l₁ l₂ l₃} →
         (Flat (MaxBoolRes l₁ l₂ l₃) ⟦×⟧
           (⟦Bool⟧ l₁ ⟦×⟧ ⟦Bool⟧ l₂)) ==> ⟦Bool⟧ l₃
⟦and⟧ .mor (maxBoolRes _ U-U ,   x , y) = x and y
⟦and⟧ .mor (maxBoolRes _ U-Ex ,  x , y) = constraint x and y
⟦and⟧ .mor (maxBoolRes _ Ex-U ,  x , y) = x and constraint y
⟦and⟧ .mor (maxBoolRes _ Ex-Ex , x , y) = x and y

⟦or⟧ : ∀ {l₁ l₂ l₃} →
         (Flat (MaxBoolRes l₁ l₂ l₃) ⟦×⟧
           (⟦Bool⟧ l₁ ⟦×⟧ ⟦Bool⟧ l₂)) ==> ⟦Bool⟧ l₃
⟦or⟧ .mor (maxBoolRes _ U-U ,   x , y) = x or y
⟦or⟧ .mor (maxBoolRes _ U-Ex ,  x , y) = constraint x or y
⟦or⟧ .mor (maxBoolRes _ Ex-U ,  x , y) = x or constraint y
⟦or⟧ .mor (maxBoolRes _ Ex-Ex , x , y) = x or y

⟦const⟧ : ∀ {l} → ℚ → Flat (NumConstRel l) ==> ⟦Num⟧ l
⟦const⟧ q .mor const = q

⟦extFunc⟧ : ∀ {l₁ l₂} → (Flat (FuncRel l₁ l₂) ⟦×⟧ (⟦Num⟧ l₁)) ==> LiftM (⟦Num⟧ l₂)
⟦extFunc⟧ .mor (linear-linear , exp) =
  let-linexp exp (let-funexp {- f -} zero (return (var 1ℚ zero)))

⟦if⟧ : ∀ {X b} → ((LiftM X ⟦×⟧ LiftM X) ⟦×⟧ (Flat (IfRes b) ⟦×⟧ (⟦Bool⟧ b))) ==> LiftM X
⟦if⟧ .mor ((tr , fa) , (ifRes _ , ϕ)) = if ϕ tr fa

⟦Index⟧ : ℕ → ⟦Type⟧
⟦Index⟧ n = Flat (Fin n)

⟦∃⟧ : ∀ {l p₁ p₂} →
     (Flat (QuantRes l p₁ p₂) ⟦×⟧ (⟦Num⟧ l ⟦⇒⟧ LiftM (⟦Bool⟧ p₁))) ==> ⟦Bool⟧ p₂
⟦∃⟧ .mor {Δ} (quantRes U , f) =
  ex (compile (bind-let (f (Δ ,∙) succ (var 1ℚ zero))
                                     λ Δ' ρ ϕ → return (constraint ϕ)))
⟦∃⟧ .mor {Δ} (quantRes Ex , f) =
  ex (compile (f (Δ ,∙) succ (var 1ℚ zero)))

ℳ : Model verifierRestriction (suc 0ℓ) 0ℓ
ℳ .Model.⟦Type⟧ = ⟦Type⟧
ℳ .Model._==>_ = _==>_
ℳ .Model.Flat = Flat
ℳ .Model.elem a .mor _ = a
ℳ .Model.Flat-map = Flat-map
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
ℳ .Model.⟦not⟧ = ⟦not⟧
ℳ .Model.⟦and⟧ = ⟦and⟧
ℳ .Model.⟦or⟧ = ⟦or⟧
ℳ .Model.⟦≤⟧ = ⟦≤⟧
ℳ .Model.⟦<⟧ = ⟦<⟧
ℳ .Model.⟦if⟧ = ⟦if⟧
ℳ .Model.⟦∃⟧ = ⟦∃⟧

open import MiniVehicle.Language.Interpretation verifierRestriction ℳ
open import MiniVehicle.Language.Syntax verifierRestriction

normalise : ε / ε ⊢ Bool (BoolRes (linear , Ex)) → PrenexFormula ε
normalise t = toPrenexForm (compile (⟦ t ⟧tm (lift tt) .mor tt))
