module MiniVehicle.Verifiers.Normalisation where

open import Level using (Lift; lift; lower; suc; 0ℓ)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; proj₁; proj₂; _,_; Σ-syntax)
open import Data.Rational using (ℚ; 1ℚ; _+_; _*_)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import MiniVehicle.Language.Syntax.Restriction
open import MiniVehicle.Language.Model
open import MiniVehicle.Verifiers.Syntax.Restriction
open import VerifierLang.Syntax
open import VerifierLang.Semantics
open import Util.EquiInhabited

------------------------------------------------------------------------------
-- Normalisation to ExFormula

data ExFormula : LinVarCtxt → Set where
  constraint : ∀ {Δ} → Constraint Δ → ExFormula Δ
  ex         : ∀ {Δ} → ExFormula (Δ ,∙) → ExFormula Δ
  _and_      : ∀ {Δ} → ExFormula Δ → ExFormula Δ → ExFormula Δ
  _or_       : ∀ {Δ} → ExFormula Δ → ExFormula Δ → ExFormula Δ

rename-ExFormula : Renameable ExFormula
rename-ExFormula ρ (constraint ϕ) = constraint (rename-Constraint ρ ϕ)
rename-ExFormula ρ (ex ϕ)         = ex (rename-ExFormula (under ρ) ϕ)
rename-ExFormula ρ (ϕ and ψ)      = rename-ExFormula ρ ϕ and rename-ExFormula ρ ψ
rename-ExFormula ρ (ϕ or ψ)       = rename-ExFormula ρ ϕ or rename-ExFormula ρ ψ

data BoolExpr (Δ : LinVarCtxt) : Set where
  constraint : Constraint Δ → BoolExpr Δ
  _and_ : BoolExpr Δ → BoolExpr Δ → BoolExpr Δ
  _or_  : BoolExpr Δ → BoolExpr Δ → BoolExpr Δ

rename-BoolExpr : Renameable BoolExpr
rename-BoolExpr ρ (constraint ϕ) = constraint (rename-Constraint ρ ϕ)
rename-BoolExpr ρ (ϕ and ψ)      = rename-BoolExpr ρ ϕ and rename-BoolExpr ρ ψ
rename-BoolExpr ρ (ϕ or ψ)       = rename-BoolExpr ρ ϕ or rename-BoolExpr ρ ψ

negate-BoolExpr : ∀ {Δ} → BoolExpr Δ → BoolExpr Δ
negate-BoolExpr (constraint p) = constraint (negate p)
negate-BoolExpr (p and q) = negate-BoolExpr p or negate-BoolExpr q
negate-BoolExpr (p or q) = negate-BoolExpr p and negate-BoolExpr q

cast : ∀ {Δ} → BoolExpr Δ → ExFormula Δ
cast (constraint x) = constraint x
cast (p and q) = cast p and cast q
cast (p or q) = cast p and cast q

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
⟦Bool⟧ (_ , U) .Carrier = BoolExpr
⟦Bool⟧ (_ , U) .rename = rename-BoolExpr

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

data LetLift (A : LinVarCtxt → Set) : LinVarCtxt → Set where
  return     : ∀ {Δ} → A Δ → LetLift A Δ
  if         : ∀ {Δ} → BoolExpr Δ → LetLift A Δ → LetLift A Δ → LetLift A Δ
  let-linexp : ∀ {Δ} → LinExp Δ → LetLift A (Δ ,∙) → LetLift A Δ
  let-funexp : ∀ {Δ} → {- fsymb → -} Var Δ → LetLift A (Δ ,∙) → LetLift A Δ

-- expand a ExFormula within lets and ifs into a ExFormula
compile : ∀ {Δ} → LetLift ExFormula Δ → ExFormula Δ
compile (return x)       = x
compile (if ϕ tr fa)     = ((cast ϕ) and (compile tr)) or (cast (negate-BoolExpr ϕ) and (compile fa))
compile (let-linexp e k) = ex ((constraint ((1ℚ `*`var zero) `=` rename-LinExp succ e)) and compile k)
compile (let-funexp x k) = ex ((constraint (zero `=`f (succ x))) and (compile k))

rename-lift : ∀ {A} → Renameable A → Renameable (LetLift A)
rename-lift rA ρ (return x) =
  return (rA ρ x)
rename-lift rA ρ (if p k₁ k₂) =
  if (rename-BoolExpr ρ p) (rename-lift rA ρ k₁) (rename-lift rA ρ k₂)
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
⟦≤⟧ .mor (compRes const-const ,   x , y) = constraint (const x `≤` const y)
⟦≤⟧ .mor (compRes const-linear ,  x , y) = constraint (const x `≤` y)
⟦≤⟧ .mor (compRes linear-const ,  x , y) = constraint (x `≤` const y)
⟦≤⟧ .mor (compRes linear-linear , x , y) = constraint (x `≤` y)

⟦<⟧ : ∀ {l₁ l₂ l₃} → (Flat (CompRes l₁ l₂ l₃) ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Bool⟧ l₃
⟦<⟧ .mor (compRes const-const ,   x , y) = constraint (const x `<` const y)
⟦<⟧ .mor (compRes const-linear ,  x , y) = constraint (const x `<` y)
⟦<⟧ .mor (compRes linear-const ,  x , y) = constraint (x `<` const y)
⟦<⟧ .mor (compRes linear-linear , x , y) = constraint (x `<` y)

⟦not⟧ : ∀ {p₁ p₂} → (Flat (NotRes p₁ p₂) ⟦×⟧ ⟦Bool⟧ p₁) ==> ⟦Bool⟧ p₂
⟦not⟧ .mor (notRes U , x) = negate-BoolExpr x

⟦and⟧ : ∀ {l₁ l₂ l₃} →
         (Flat (MaxBoolRes l₁ l₂ l₃) ⟦×⟧
           (⟦Bool⟧ l₁ ⟦×⟧ ⟦Bool⟧ l₂)) ==> ⟦Bool⟧ l₃
⟦and⟧ .mor (maxBoolRes _ U-U ,   x , y) = x and y
⟦and⟧ .mor (maxBoolRes _ U-Ex ,  x , y) = cast x and y
⟦and⟧ .mor (maxBoolRes _ Ex-U ,  x , y) = x and cast y
⟦and⟧ .mor (maxBoolRes _ Ex-Ex , x , y) = x and y

⟦or⟧ : ∀ {l₁ l₂ l₃} →
         (Flat (MaxBoolRes l₁ l₂ l₃) ⟦×⟧
           (⟦Bool⟧ l₁ ⟦×⟧ ⟦Bool⟧ l₂)) ==> ⟦Bool⟧ l₃
⟦or⟧ .mor (maxBoolRes _ U-U ,   x , y) = x or y
⟦or⟧ .mor (maxBoolRes _ U-Ex ,  x , y) = cast x or y
⟦or⟧ .mor (maxBoolRes _ Ex-U ,  x , y) = x or cast y
⟦or⟧ .mor (maxBoolRes _ Ex-Ex , x , y) = x or y

⟦const⟧ : ∀ {l} → ℚ → Flat (NumConstRel l) ==> ⟦Num⟧ l
⟦const⟧ q .mor const = q

⟦if⟧ : ∀ {X b} → ((LiftM X ⟦×⟧ LiftM X) ⟦×⟧ (Flat (IfRes b) ⟦×⟧ (⟦Bool⟧ b))) ==> LiftM X
⟦if⟧ .mor ((tr , fa) , (ifRes _ , ϕ)) = if ϕ tr fa

⟦Index⟧ : ℕ → ⟦Type⟧
⟦Index⟧ n = Flat (Fin n)

⟦∃⟧ : ∀ {l p₁ p₂} →
     (Flat (QuantRes l p₁ p₂) ⟦×⟧ (⟦Num⟧ l ⟦⇒⟧ LiftM (⟦Bool⟧ p₁))) ==> ⟦Bool⟧ p₂
⟦∃⟧ .mor {Δ} (quantRes U , f) =
  ex (compile (bind-let (f (Δ ,∙) succ (1ℚ `*`var zero))
                                     λ Δ' ρ ϕ → return (cast ϕ)))
⟦∃⟧ .mor {Δ} (quantRes Ex , f) =
  ex (compile (f (Δ ,∙) succ (1ℚ `*`var zero)))

ℳ : Model verifierRestriction (suc 0ℓ) 0ℓ
ℳ .Model.⟦Type⟧ = ⟦Type⟧
ℳ .Model._==>_ = _==>_
ℳ .Model.Flat = Flat
ℳ .Model.elem a .mor _ = a
ℳ .Model.Flat-map = Flat-map
ℳ .Model.⟦id⟧ = ⟦id⟧
ℳ .Model._∘_ = _∘S_
ℳ .Model._⟦×⟧_ = _⟦×⟧_
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
ℳ .Model.⟦Bool⟧ = ⟦Bool⟧
ℳ .Model.⟦not⟧ = ⟦not⟧
ℳ .Model.⟦and⟧ = ⟦and⟧
ℳ .Model.⟦or⟧ = ⟦or⟧
ℳ .Model.⟦≤⟧ = ⟦≤⟧
ℳ .Model.⟦<⟧ = ⟦<⟧
ℳ .Model.⟦if⟧ = ⟦if⟧
ℳ .Model.⟦∃⟧ = ⟦∃⟧

-- representation of the external function
⟦extFunc⟧ : (⟦Num⟧ linear ⟦⇒⟧ LiftM (⟦Num⟧ linear)) .Carrier ε
⟦extFunc⟧ Δ' ρ exp = let-linexp exp (let-funexp {- f -} zero (return (1ℚ `*`var zero)))

------------------------------------------------------------------------------
-- QuerySet
private
  variable
    Δ Δ₁ Δ₂ : LinVarCtxt

liftQuery : ∀ {Δ} → Query Δ → Query ε
liftQuery {ε}    b = b
liftQuery {Δ ,∙} b = liftQuery (ex b)

and-QueryBody : QueryBody Δ → Query Δ → Query Δ
and-QueryBody x (body y) = body (x and y)
and-QueryBody x (ex y) = ex (and-QueryBody (rename-QueryBody succ x) y)

and-Query : Query Δ → Query Δ → Query Δ
and-Query (ex x) y = ex (and-Query x (rename-Query succ y))
and-Query (body x) y = and-QueryBody x y

and-QuerySet : QuerySet → QuerySet → QuerySet
and-QuerySet (query x) (query y) = query (and-Query x y)
and-QuerySet (ps or ps₁) qs = and-QuerySet ps qs or and-QuerySet ps₁ qs
and-QuerySet ps (qs₁ or qs₂) = and-QuerySet ps qs₁ or and-QuerySet ps qs₂

quantify-QuerySet : QuerySet → QuerySet
quantify-QuerySet (query x)  = query (ex (rename-Query succ x))
quantify-QuerySet (ϕ₁ or ϕ₂) = quantify-QuerySet ϕ₁ or quantify-QuerySet ϕ₂

toQuerySet : ExFormula Δ → QuerySet
toQuerySet (constraint c) = query (liftQuery (body (constraint c)))
toQuerySet (ϕ and ψ)      = and-QuerySet (toQuerySet ϕ) (toQuerySet ψ)
toQuerySet (ϕ or ψ)       = _or_ (toQuerySet ϕ) (toQuerySet ψ)
toQuerySet (ex ϕ)         = quantify-QuerySet (toQuerySet ϕ)

toQueryTree : ExFormula ε → QueryTree
toQueryTree (ϕ and ψ)      = toQueryTree ϕ and toQueryTree ψ
toQueryTree (ϕ or ψ)       = toQueryTree ϕ or toQueryTree ψ
toQueryTree (ex ϕ)         = querySet false (toQuerySet (ex ϕ))
toQueryTree (constraint ϕ) = querySet false (toQuerySet (constraint ϕ))

------------------------------------------------------------------------------
-- Compilation

open import MiniVehicle.Language.Syntax verifierRestriction
open import MiniVehicle.Language.Interpretation verifierRestriction ℳ

normalise : NetworkSpecification linear (linear , Ex) → QueryTree
normalise t = toQueryTree (compile (⟦ t ⟧tm (lift tt) .mor (tt , ⟦extFunc⟧)))
