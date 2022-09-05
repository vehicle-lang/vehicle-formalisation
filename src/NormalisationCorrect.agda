{-# OPTIONS --postfix-projections #-}

module NormalisationCorrect where

open import Level using (0ℓ; suc) -- ; Lift; lift; lower)

open import Data.Bool using (not; _∧_; _∨_; true; false)
                   renaming (Bool to 𝔹; T to True; if_then_else_ to ifᵇ_then_else_)
open import Data.Bool.Properties using (∨-identityʳ)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Rational using (ℚ; _+_; _*_; _≤ᵇ_; _≟_; 1ℚ)
open import Data.Rational.Properties using (*-identityˡ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; sym; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

open import MiniVehicle hiding (_⇒ᵣ_)
open import NormalisedExpr
open import Interpretation
open import Isomorphism

import StandardSemantics as S
import Normalisation as N

is-true-or-false : ∀ b → (b ≡ true) ⊎ (b ≡ false)
is-true-or-false false = inj₂ refl
is-true-or-false true = inj₁ refl


------------------------------------------------------------------------------
record World : Set where
  field
    ctxt : LinVarCtxt
    env  : Env ctxt
open World

empty : World
empty .ctxt = ε

-- World morphisms extend the context whilst making sure that the
-- environment is preserved.
record _⇒w_ (w₁ w₂ : World) : Set where
  field
    ren   : w₁ .ctxt ⇒ᵣ w₂ .ctxt
    presv : ∀ x → w₁ .env (ren x) ≡ w₂ .env x
open _⇒w_

id-w : ∀ {w} → w ⇒w w
id-w .ren x = x
id-w .presv x = refl

_∘w_ : ∀ {w₁ w₂ w₃} → w₂ ⇒w w₃ → w₁ ⇒w w₂ → w₁ ⇒w w₃
(f ∘w g) .ren x = g .ren (f .ren x)
(f ∘w g) .presv x = trans (g .presv (f .ren x)) (f .presv x)

-- FIXME: move to NormalisationExpr
extend-env : ∀ {Δ} → Env Δ → ℚ → Env (Δ ,∙)
extend-env η q zero     = q
extend-env η q (succ x) = η x

extend-w : World → ℚ → World
extend-w w q .ctxt = w .ctxt ,∙
extend-w w q .env = extend-env (w .env) q

under-w : ∀ {w₁ w₂ q} → (w₁ ⇒w w₂) → (extend-w w₁ q ⇒w extend-w w₂ q)
under-w ρ .ren = NormalisedExpr.under (ρ .ren)
under-w ρ .presv zero = refl
under-w ρ .presv (succ x) = ρ .presv x

under-w' : ∀ {w₁ w₂ q₁ q₂} → (q₁ ≡ q₂) → (w₁ ⇒w w₂) → (extend-w w₁ q₁ ⇒w extend-w w₂ q₂)
under-w' eq ρ .ren = NormalisedExpr.under (ρ .ren)
under-w' eq ρ .presv zero = eq
under-w' eq ρ .presv (succ x) = ρ .presv x

wk-w : ∀ {w q} → extend-w w q ⇒w w
wk-w .ren = succ
wk-w .presv x = refl

------------------------------------------------------------------------------
-- Our category of related interpretations

-- module 𝒮 = Model (S.ℳ extFunc)
module 𝒩 = Model N.ℳ


record WRel : Set (suc 0ℓ) where
  field
    Left  : Set 0ℓ
    Right : 𝒩.⟦Type⟧
    rel   : (w : World) → Left → Right .N.Carrier (w .ctxt) → Set
    ext   : ∀ {w w'} (ρ : w' ⇒w w) a b → rel w a b → rel w' a (Right .N.rename (ρ .ren) b)
open WRel

record _===>_ (X Y : WRel) : Set where
  field
    left  : X .Left → Y .Left
    right : X .Right N.==> Y .Right
    rel-mor   : ∀ w lx rx → X .rel w lx rx → Y .rel w (left lx) (right .N.mor rx)
open _===>_

------------------------------------------------------------------------------
-- Composition

_∘R_ : ∀ {X Y Z} → (Y ===> Z) → (X ===> Y) → (X ===> Z)
(f ∘R g) .left x = f .left (g .left x)
(f ∘R g) .right = f .right 𝒩.∘ g .right
(f ∘R g) .rel-mor w x₁ x₂ r-x₁x₂ = f .rel-mor w _ _ (g .rel-mor w _ _ r-x₁x₂)

⟦id⟧R : ∀ {X} → X ===> X
⟦id⟧R .left x = x
⟦id⟧R .right = 𝒩.⟦id⟧
⟦id⟧R .rel-mor w x₁ x₂ r = r

------------------------------------------------------------------------------
-- Products and terminal object
⟦⊤⟧R : WRel
⟦⊤⟧R .Left = ⊤
⟦⊤⟧R .Right = 𝒩.⟦⊤⟧
⟦⊤⟧R .rel w tt tt = ⊤
⟦⊤⟧R .ext ρ tt tt x = x

⟦terminal⟧R : ∀ {X} → X ===> ⟦⊤⟧R
⟦terminal⟧R .left _ = tt
⟦terminal⟧R .right = 𝒩.⟦terminal⟧
⟦terminal⟧R .rel-mor _ _ _ _ = tt

_⟦×⟧R_ : WRel → WRel → WRel
(X ⟦×⟧R Y) .Left = X .Left × Y .Left
(X ⟦×⟧R Y) .Right = X .Right 𝒩.⟦×⟧ Y .Right
(X ⟦×⟧R Y) .rel w (x , y) (x' , y') = X .rel w x x' × Y .rel w y y'
(X ⟦×⟧R Y) .ext ρ (x , y) (x' , y') (r₁ , r₂) =
  (X .ext ρ x x' r₁) , (Y .ext ρ y y' r₂)

⟨_,_⟩R : ∀ {X Y Z} → (X ===> Y) → (X ===> Z) → (X ===> (Y ⟦×⟧R Z))
⟨ f , g ⟩R .left x = (f .left x) , (g .left x)
⟨ f , g ⟩R .right = 𝒩.⟨ f .right , g .right ⟩
⟨ f , g ⟩R .rel-mor w x₁ x₂ r-x₁x₂ =
  f .rel-mor w x₁ x₂ r-x₁x₂ ,
  g .rel-mor w x₁ x₂ r-x₁x₂

⟦proj₁⟧R : ∀ {X Y} → (X ⟦×⟧R Y) ===> X
⟦proj₁⟧R .left = proj₁
⟦proj₁⟧R .right = 𝒩.⟦proj₁⟧
⟦proj₁⟧R .rel-mor w _ _ r = r .proj₁

⟦proj₂⟧R : ∀ {X Y} → (X ⟦×⟧R Y) ===> Y
⟦proj₂⟧R .left = proj₂
⟦proj₂⟧R .right = 𝒩.⟦proj₂⟧
⟦proj₂⟧R .rel-mor w _ _ r = r .proj₂

------------------------------------------------------------------------------
-- Functions and Universal Quantification

-- FIXME: disconnect functions and forall from LiftMR; make the
-- parameterised semantics put them together
_⟦⇒⟧R_ : WRel → WRel → WRel
(X ⟦⇒⟧R Y) .Left = X .Left → Y .Left
(X ⟦⇒⟧R Y) .Right = X .Right 𝒩.⟦⇒⟧ Y .Right
(X ⟦⇒⟧R Y) .rel w f g =
  ∀ w' (ρ : w' ⇒w w) x y →
     X .rel w' x y →
     Y .rel w' (f x) (g (w' .ctxt) (ρ .ren) y)
(X ⟦⇒⟧R Y) .ext ρ f g r =
  λ w'' ρ' x y → r w'' (ρ ∘w ρ') x y

⟦Λ⟧R : ∀ {X Y Z} → ((X ⟦×⟧R Y) ===> Z) → (X ===> (Y ⟦⇒⟧R Z))
⟦Λ⟧R {X} f .left x y = f .left (x , y)
⟦Λ⟧R {X} f .right = 𝒩.⟦Λ⟧ (f .right)
⟦Λ⟧R {X} f .rel-mor w x₁ x₂ r-x₁x₂ w' ρ y₁ y₂ r-y₁y₂ =
  f .rel-mor w' (x₁ , y₁)
                (X .Right .N.rename (ρ .ren) x₂ , y₂)
                (X .ext ρ x₁ x₂ r-x₁x₂ , r-y₁y₂)

⟦eval⟧R : ∀ {X Y} → ((X ⟦⇒⟧R Y) ⟦×⟧R X) ===> Y
⟦eval⟧R .left (f , x) = f x
⟦eval⟧R .right = 𝒩.⟦eval⟧
⟦eval⟧R .rel-mor w (f₁ , x₁) (f₂ , x₂) (r-f₁f₂ , r-x₁x₂) =
  r-f₁f₂ w id-w x₁ x₂ r-x₁x₂

⟦∀⟧R : (ℕ → WRel) → WRel
⟦∀⟧R A .Left = ∀ n → A n .Left
⟦∀⟧R A .Right = 𝒩.⟦∀⟧ (λ n → A n .Right)
⟦∀⟧R A .rel w x y = ∀ n → A n .rel w (x n) (y n)
⟦∀⟧R A .ext ρ x y r n = A n .ext ρ (x n) (y n) (r n)

⟦∀-intro⟧R : ∀ {X A} → (∀ n → X ===> A n) → X ===> ⟦∀⟧R A
⟦∀-intro⟧R f .left x n = f n .left x
⟦∀-intro⟧R f .right = 𝒩.⟦∀-intro⟧ (λ n → f n .right)
⟦∀-intro⟧R f .rel-mor w x₁ x₂ r n = f n .rel-mor w x₁ x₂ r

⟦∀-elim⟧R : ∀ {A} n → ⟦∀⟧R A ===> A n
⟦∀-elim⟧R n .left f = f n
⟦∀-elim⟧R n .right = 𝒩.⟦∀-elim⟧ n
⟦∀-elim⟧R n .rel-mor w f₁ f₂ r = r n

------------------------------------------------------------------------------
KR : Set → WRel
KR X .Left = X
KR X .Right = N.K X
KR X .rel w x y = x ≡ y
KR X .ext ρ x y eq = eq

⟦Index⟧R : ℕ → WRel
⟦Index⟧R n = KR (Fin n)

module _ (extFunc : ℚ → ℚ) where

  module 𝒮 = Model (S.ℳ extFunc)

  ext-evalLinExp :
    ∀ {w₁ w₂} e (ρ : w₂ ⇒w w₁) →
      eval-LinExp e (w₁ .env) ≡ eval-LinExp (rename-LinExp (ρ .ren) e) (w₂ .env)
  ext-evalLinExp (const q)   ρ = refl
  ext-evalLinExp (var q x)   ρ = cong (λ □ → q * □) (sym (ρ .presv x))
  ext-evalLinExp (e₁ `+` e₂) ρ = cong₂ _+_ (ext-evalLinExp e₁ ρ) (ext-evalLinExp e₂ ρ)

  ext-evalConstraint :
    ∀ {w₁ w₂} p (ρ : w₂ ⇒w w₁) →
      eval-ConstraintExp extFunc p (w₁ .env)
      ≡ eval-ConstraintExp extFunc (rename-ConstraintExp (ρ .ren) p) (w₂ .env)
  ext-evalConstraint (e₁ `≤` e₂) ρ rewrite ext-evalLinExp e₁ ρ rewrite ext-evalLinExp e₂ ρ = refl
  ext-evalConstraint (e₁ `>` e₂) ρ rewrite ext-evalLinExp e₁ ρ rewrite ext-evalLinExp e₂ ρ = refl
  ext-evalConstraint (e₁ `=` e₂) ρ rewrite ext-evalLinExp e₁ ρ rewrite ext-evalLinExp e₂ ρ = refl
  ext-evalConstraint (e₁ `≠` e₂) ρ rewrite ext-evalLinExp e₁ ρ rewrite ext-evalLinExp e₂ ρ = refl
  ext-evalConstraint (p and q)   ρ rewrite ext-evalConstraint p ρ rewrite ext-evalConstraint q ρ = refl
  ext-evalConstraint (p or q)    ρ rewrite ext-evalConstraint p ρ rewrite ext-evalConstraint q ρ = refl
  ext-evalConstraint (x `=`f y)  ρ rewrite ρ .presv x rewrite ρ .presv y = refl
  ext-evalConstraint (x `≠`f y)  ρ rewrite ρ .presv x rewrite ρ .presv y = refl

  ------------------------------------------------------------------------------
  -- Numbers, and linear expressions
  ⟦Num⟧R : Linearity → WRel
  ⟦Num⟧R const = KR ℚ
  ⟦Num⟧R linear .Left = ℚ
  ⟦Num⟧R linear .Right = 𝒩.⟦Num⟧ linear
  ⟦Num⟧R linear .rel w x exp = x ≡ eval-LinExp exp (w .env)
  ⟦Num⟧R linear .ext ρ x exp eq = trans eq (ext-evalLinExp exp ρ)

  ⟦num⟧R : ∀ {X} → ℚ → X ===> ⟦Num⟧R const
  ⟦num⟧R q .left _ = q
  ⟦num⟧R q .right = 𝒩.⟦num⟧ q
  ⟦num⟧R q .rel-mor w _ _ _ = refl

  ⟦add⟧R : (⟦Num⟧R linear ⟦×⟧R ⟦Num⟧R linear) ===> ⟦Num⟧R linear
  ⟦add⟧R .left = 𝒮.⟦add⟧
  ⟦add⟧R .right = 𝒩.⟦add⟧
  ⟦add⟧R .rel-mor w (x₁ , y₁) (x₂ , y₂) (r-x₁x₂ , r-y₁y₂) =
    cong₂ _+_ r-x₁x₂ r-y₁y₂

  ⟦mul⟧R : (⟦Num⟧R const ⟦×⟧R ⟦Num⟧R linear) ===> ⟦Num⟧R linear
  ⟦mul⟧R .left = 𝒮.⟦mul⟧
  ⟦mul⟧R .right = 𝒩.⟦mul⟧
  ⟦mul⟧R .rel-mor w (x₁ , y₁) (x₂ , y₂) (r-x₁x₂ , r-y₁y₂) =
    trans (cong₂ _*_ r-x₁x₂ r-y₁y₂) (eval-⊛ x₂ y₂ (w .env))

  ⟦const⟧R : ⟦Num⟧R const ===> ⟦Num⟧R linear
  ⟦const⟧R .left = 𝒮.⟦const⟧
  ⟦const⟧R .right = 𝒩.⟦const⟧
  ⟦const⟧R .rel-mor w _ _ eq = eq

  ------------------------------------------------------------------------------
  -- Booleans and constraints
  Constraint-WRel : WRel
  Constraint-WRel .Left = 𝒮.⟦Bool⟧ constraint
  Constraint-WRel .Right = 𝒩.⟦Bool⟧ constraint
  Constraint-WRel .rel w b ϕ = b ≡ eval-ConstraintExp extFunc ϕ (w .env)
  Constraint-WRel .ext ρ b ϕ eq = trans eq (ext-evalConstraint ϕ ρ)

  data QueryR : ∀ w → S.Ex 𝔹 → Query (w .ctxt) → Set where
    q-constraint : ∀ {w b ϕ} →
                   eval-ConstraintExp extFunc ϕ (w .env) ≡ b →
                   QueryR w (S.return b) (constraint ϕ)
    q-true       : ∀ {w x ϕ ψ₁ ψ₂} →
                   eval-ConstraintExp extFunc ϕ (w .env) ≡ true →
                   QueryR w x ψ₁ →
                   QueryR w x ((constraint ϕ and ψ₁) or (constraint (negate ϕ) and ψ₂))
    q-false      : ∀ {w x ϕ ψ₁ ψ₂} →
                   eval-ConstraintExp extFunc ϕ (w .env) ≡ false →
                   QueryR w x ψ₂ →
                   QueryR w x ((constraint ϕ and ψ₁) or (constraint (negate ϕ) and ψ₂))
    q-ex         : ∀ {w k ϕ}   → (∀ q → QueryR (extend-w w q) (k q) ϕ) → QueryR w (S.ex k) (ex ϕ)
    q-ex'        : ∀ {w x ϕ ψ} q →
                   (∀ q' → (q' ≡ q) ↔ True (eval-ConstraintExp extFunc ϕ (extend-env (w .env) q'))) →
                   QueryR (extend-w w q) x ψ →
                   QueryR w x (ex (constraint ϕ and ψ))

  ext-Query : ∀ {w₁ w₂} (ρ : w₂ ⇒w w₁) x₁ x₂ →
              QueryR w₁ x₁ x₂ → QueryR w₂ x₁ (rename-Query (ρ .ren) x₂)
  ext-Query ρ _ _ (q-constraint {ϕ = ϕ} x) =
    q-constraint (trans (sym (ext-evalConstraint ϕ ρ)) x)
  ext-Query ρ _ _ (q-true {ϕ = ϕ} is-true r) rewrite rename-negate (ρ .ren) ϕ =
    q-true (trans (sym (ext-evalConstraint ϕ ρ)) is-true) (ext-Query ρ _ _ r)
  ext-Query ρ _ _ (q-false {ϕ = ϕ} is-false r) rewrite rename-negate (ρ .ren) ϕ =
    q-false (trans (sym (ext-evalConstraint ϕ ρ)) is-false) (ext-Query ρ _ _ r)
  ext-Query ρ _ _ (q-ex r) = q-ex λ q → ext-Query (under-w ρ) _ _ (r q)
  ext-Query ρ _ _ (q-ex' {ϕ = ϕ} q uniq r) =
    q-ex' q (λ q' → ↔-trans (uniq q') (cong-True (ext-evalConstraint ϕ (under-w ρ))))
          (ext-Query (under-w ρ) _ _ r)

  ⟦Bool⟧R : BoolKind → WRel
  ⟦Bool⟧R constraint = Constraint-WRel
  ⟦Bool⟧R query .Left = 𝒮.⟦Bool⟧ query
  ⟦Bool⟧R query .Right = 𝒩.⟦Bool⟧ query
  ⟦Bool⟧R query .rel = QueryR
  ⟦Bool⟧R query .ext = ext-Query

  ⟦≤⟧R : (⟦Num⟧R linear ⟦×⟧R ⟦Num⟧R linear) ===> ⟦Bool⟧R constraint
  ⟦≤⟧R .left = 𝒮.⟦≤⟧
  ⟦≤⟧R .right = 𝒩.⟦≤⟧
  ⟦≤⟧R .rel-mor w (x₁ , y₁) (x₂ , y₂) (r-x₁x₂ , r-y₁y₂) =
    cong₂ _≤ᵇ_ r-x₁x₂ r-y₁y₂

  ⟦and⟧R : (⟦Bool⟧R constraint ⟦×⟧R ⟦Bool⟧R constraint) ===> ⟦Bool⟧R constraint
  ⟦and⟧R .left = 𝒮.⟦and⟧
  ⟦and⟧R .right = 𝒩.⟦and⟧
  ⟦and⟧R .rel-mor w (x₁ , y₁) (x₂ , y₂) (r-x₁x₂ , r-y₁y₂) =
    cong₂ _∧_ r-x₁x₂ r-y₁y₂

  ⟦or⟧R : (⟦Bool⟧R constraint ⟦×⟧R ⟦Bool⟧R constraint) ===> ⟦Bool⟧R constraint
  ⟦or⟧R .left = 𝒮.⟦or⟧
  ⟦or⟧R .right = 𝒩.⟦or⟧
  ⟦or⟧R .rel-mor w (x₁ , y₁) (x₂ , y₂) (r-x₁x₂ , r-y₁y₂) =
    cong₂ _∨_ r-x₁x₂ r-y₁y₂

  ⟦not⟧R : ⟦Bool⟧R constraint ===> ⟦Bool⟧R constraint
  ⟦not⟧R .left = 𝒮.⟦not⟧
  ⟦not⟧R .right = 𝒩.⟦not⟧
  ⟦not⟧R .rel-mor w x₁ x₂ r-x₁x₂ =
    trans (cong not r-x₁x₂) (eval-negate extFunc x₂ (w .env))

  ------------------------------------------------------------------------------
  module _ (X : WRel) where

    LetLiftR : (w : World) → X .Left → LetLift (X .Right .N.Carrier) (w .ctxt) → Set
    LetLiftR w a (return b) = X .rel w a b
    LetLiftR w a (if c k₁ k₂) =
      ifᵇ (eval-ConstraintExp extFunc c (w .env))
       then LetLiftR w a k₁
       else LetLiftR w a k₂
    LetLiftR w a (let-linexp e k) =
      LetLiftR (extend-w w (eval-LinExp e (w .env))) a k
    LetLiftR w a (let-funexp x k) =
      LetLiftR (extend-w w (extFunc (w .env x))) a k

    ext-lift : ∀ {w₁ w₂} (ρ : w₂ ⇒w w₁) la lb →
               LetLiftR w₁ la lb →
               LetLiftR w₂ la (rename-lift (X .Right .N.rename) (ρ .ren) lb)
    ext-lift ρ a (return b) = X .ext ρ a b
    ext-lift {w₁} ρ a (if c tru fal) rewrite sym (ext-evalConstraint c ρ) with eval-ConstraintExp extFunc c (w₁ .env)
    ... | false = ext-lift ρ a fal
    ... | true  = ext-lift ρ a tru
    ext-lift ρ a (let-linexp x lb) =
      ext-lift (record { ren = NormalisedExpr.under (ρ .ren)
                       ; presv = λ { zero → sym (ext-evalLinExp x ρ)
                                   ; (succ x₁) → ρ .presv x₁ } }) a lb
    ext-lift ρ a (let-funexp x lb) =
      ext-lift (record { ren = NormalisedExpr.under (ρ .ren)
                       ; presv = λ { zero → cong extFunc (ρ .presv x)
                                   ; (succ x₁) → ρ .presv x₁ } }) a lb

    LiftMR : WRel
    LiftMR .Left = X .Left
    LiftMR .Right = 𝒩.Mon (X .Right)
    LiftMR .rel = LetLiftR
    LiftMR .ext = ext-lift

  eval-Lift : ∀ {Δ} → LetLift (𝒩.⟦Bool⟧ constraint .N.Carrier) Δ → Env Δ → 𝔹
  eval-Lift (return x) η = eval-ConstraintExp extFunc x η
  eval-Lift (if x x₁ x₂) η = ifᵇ (eval-ConstraintExp extFunc x η) then eval-Lift x₁ η else eval-Lift x₂ η
  eval-Lift (let-linexp x x₁) η = eval-Lift x₁ (extend-env η (eval-LinExp x η))
  eval-Lift (let-funexp x x₁) η = eval-Lift x₁ (extend-env η (extFunc (η x)))

  lift-correct : ∀ {w b} e → LetLiftR Constraint-WRel w b e → b ≡ eval-Lift e (w .env)
  lift-correct (return x) r = r
  lift-correct {w} (if x e e₁) r with eval-ConstraintExp extFunc x (w .env)
  ... | true = lift-correct e r
  ... | false = lift-correct e₁ r
  lift-correct (let-linexp x e) r = lift-correct e r
  lift-correct (let-funexp x e) r = lift-correct e r

  let-bindR : ∀ {X Y} w x y →
    (f : X .Left → Y .Left)
    (g : (X .Right .N.Carrier ⇒ₖ LetLift (Y .Right .N.Carrier)) (w .ctxt)) →
    LetLiftR X w x y →
    (∀ w' (ρ : w' ⇒w w) a b → X .rel w' a b → LetLiftR Y w' (f a) (g (w' .ctxt) (ρ .ren) b)) →
    LetLiftR Y w (f x) (bind-let y g)
  let-bindR w x₁ (return x₂) f g r-x₁x₂ r-fg = r-fg w id-w x₁ x₂ r-x₁x₂
  let-bindR w x₁ (if c x₂₁ x₂₂) f g r-x₁x₂ r-fg with eval-ConstraintExp extFunc c (w .env)
  ... | true = let-bindR w x₁ x₂₁ f g r-x₁x₂ r-fg
  ... | false = let-bindR w x₁ x₂₂ f g r-x₁x₂ r-fg
  let-bindR w x₁ (let-linexp e x₂) f g r-x₁x₂ r-fg =
    let-bindR (extend-w w (eval-LinExp e (w .env)))
       x₁ x₂ f (λ Δ' ρ → g Δ' (wk-r ∘ ρ))
       r-x₁x₂
       λ w' ρ → r-fg w' (wk-w ∘w ρ)
  let-bindR w x₁ (let-funexp v x₂) f g r-x₁x₂ r-fg =
    let-bindR (extend-w w (extFunc (w .env v)))
       x₁ x₂ f (λ Δ' ρ → g Δ' (wk-r ∘ ρ))
       r-x₁x₂
       λ w' ρ → r-fg w' (wk-w ∘w ρ)

  ⟦return⟧R : ∀ {X} → X ===> LiftMR X
  ⟦return⟧R .left = λ x → x
  ⟦return⟧R .right = 𝒩.⟦return⟧
  ⟦return⟧R .rel-mor w x₁ x₂ r-x₁x₂ = r-x₁x₂

  ⟦extFunc⟧R : ⟦Num⟧R linear ===> LiftMR (⟦Num⟧R linear)
  ⟦extFunc⟧R .left = 𝒮.⟦extFunc⟧
  ⟦extFunc⟧R .right = 𝒩.⟦extFunc⟧
  ⟦extFunc⟧R .rel-mor w x₁ x₂ r-x₁x₂ =
    trans (cong extFunc r-x₁x₂) (sym (*-identityˡ _))

  ⟦if⟧R : ∀ {X} → ((LiftMR X ⟦×⟧R LiftMR X) ⟦×⟧R ⟦Bool⟧R constraint) ===> LiftMR X
  ⟦if⟧R .left ((tr , fa) , false) = fa
  ⟦if⟧R .left ((tr , fa) , true) = tr
  ⟦if⟧R .right = 𝒩.⟦if⟧
  ⟦if⟧R .rel-mor w ((tr₁ , fa₁) , false) ((tr₂ , fa₂) , ϕ) ((tr₁-tr₂ , fa₁-fa₂) , eq) rewrite sym eq = fa₁-fa₂
  ⟦if⟧R .rel-mor w ((tr₁ , fa₁) , true) ((tr₂ , fa₂) , ϕ) ((tr₁-tr₂ , fa₁-fa₂) , eq) rewrite sym eq = tr₁-tr₂

  extendR : ∀ {X Y Z} → ((X ⟦×⟧R Y) ===> LiftMR Z) → (X ⟦×⟧R LiftMR Y) ===> LiftMR Z
  extendR f .left = f .left
  extendR {X} f .right = 𝒩.⟦extend⟧ (f .right)
  extendR {X} f .rel-mor w (x₁ , ly₁) (x₂ , ly₂) (x₁x₂ , ly₁-ly₂) =
    let-bindR w ly₁ ly₂
      (λ y → f .left (x₁ , y))
      (λ Δ' ρ y → f .right .N.mor (X .Right .N.rename ρ x₂ , y))
      ly₁-ly₂
      λ w' ρ y₁ y₂ y₁y₂ →
        f .rel-mor w' (x₁ , y₁) (X .Right .N.rename (ρ .ren) x₂ , y₂) (X .ext ρ x₁ x₂ x₁x₂ , y₁y₂)

  ⟦constraint⟧ : ⟦Bool⟧R constraint ===> ⟦Bool⟧R query
  ⟦constraint⟧ .left = 𝒮.⟦constraint⟧
  ⟦constraint⟧ .right = 𝒩.⟦constraint⟧
  ⟦constraint⟧ .rel-mor w _ _ r = q-constraint (sym r)

  compile-lemma : ∀ w x₁ x₂ → LetLiftR (⟦Bool⟧R query) w x₁ x₂ → QueryR w x₁ (compile x₂)
  compile-lemma w x₁ (return x) r = r
  compile-lemma w x₁ (if ϕ tr fa) r with is-true-or-false (eval-ConstraintExp extFunc ϕ (w .env))
  ... | inj₁ is-true =
         q-true is-true (compile-lemma w _ tr (subst (λ □ → ifᵇ □ then _ else _) is-true r))
  ... | inj₂ is-false =
         q-false is-false (compile-lemma w _ fa (subst (λ □ → ifᵇ □ then _ else _) is-false r))
  compile-lemma w x₁ (let-linexp e k) r =
    q-ex' q
          (λ q' →
            ↔-trans (eq-cong
                      (sym (*-identityˡ q'))
                      (ext-evalLinExp e wk-w))
             (↔-sym (does-cong (1ℚ * q' ≟
                                eval-LinExp (rename-LinExp succ e) (extend-env (w .env) q')))))
          (compile-lemma (extend-w w q) x₁ k r)
    where q : ℚ
          q = eval-LinExp e (w .env)
  compile-lemma w x₁ (let-funexp x k) r =
    q-ex' q
          (λ q' → ↔-sym (does-cong (q' ≟ extFunc (w .env x))))
          (compile-lemma (extend-w w q) x₁ k r)
    where q : ℚ
          q = extFunc (w .env x)


  ⟦∃⟧ : (⟦Num⟧R linear ⟦⇒⟧R LiftMR (⟦Bool⟧R query)) ===> ⟦Bool⟧R query
  ⟦∃⟧ .left = 𝒮.⟦∃⟧
  ⟦∃⟧ .right = 𝒩.⟦∃⟧
  ⟦∃⟧ .rel-mor w tm₁ tm₂ r =
    q-ex λ q → compile-lemma (extend-w w q) (tm₁ q) (tm₂ (w .ctxt ,∙) succ (var 1ℚ zero)) (h q)
    where h : ∀ q → LetLiftR (⟦Bool⟧R query) (extend-w w q) (tm₁ q) (tm₂ (w .ctxt ,∙) succ (var 1ℚ zero))
          h q = r (extend-w w q) wk-w q (var 1ℚ zero) (sym (*-identityˡ q))

  ℳ : Model (suc 0ℓ) 0ℓ
  ℳ .Model.⟦Type⟧ = WRel
  ℳ .Model._==>_ = _===>_
  ℳ .Model.⟦id⟧ = ⟦id⟧R
  ℳ .Model._∘_ = _∘R_
  ℳ .Model._⟦×⟧_ = _⟦×⟧R_
  ℳ .Model.⟦⊤⟧ = ⟦⊤⟧R
  ℳ .Model.⟦terminal⟧ = ⟦terminal⟧R
  ℳ .Model.⟦proj₁⟧ = ⟦proj₁⟧R
  ℳ .Model.⟦proj₂⟧ = ⟦proj₂⟧R
  ℳ .Model.⟨_,_⟩ = ⟨_,_⟩R
  ℳ .Model._⟦⇒⟧_ = _⟦⇒⟧R_
  ℳ .Model.⟦Λ⟧ = ⟦Λ⟧R
  ℳ .Model.⟦eval⟧ = ⟦eval⟧R
  ℳ .Model.⟦∀⟧ = ⟦∀⟧R
  ℳ .Model.⟦∀-intro⟧ = ⟦∀-intro⟧R
  ℳ .Model.⟦∀-elim⟧ = ⟦∀-elim⟧R
  ℳ .Model.Mon = LiftMR
  ℳ .Model.⟦return⟧ = ⟦return⟧R
  ℳ .Model.⟦extend⟧ = extendR
  ℳ .Model.⟦Num⟧ = ⟦Num⟧R
  ℳ .Model.⟦add⟧ = ⟦add⟧R
  ℳ .Model.⟦mul⟧ = ⟦mul⟧R
  ℳ .Model.⟦num⟧ = ⟦num⟧R
  ℳ .Model.⟦const⟧ = ⟦const⟧R
  ℳ .Model.⟦extFunc⟧ = ⟦extFunc⟧R
  ℳ .Model.⟦Bool⟧ = ⟦Bool⟧R
  ℳ .Model.⟦not⟧ = ⟦not⟧R
  ℳ .Model.⟦and⟧ = ⟦and⟧R
  ℳ .Model.⟦or⟧ = ⟦or⟧R
  ℳ .Model.⟦≤⟧ = ⟦≤⟧R
  ℳ .Model.⟦if⟧ = ⟦if⟧R
  ℳ .Model.⟦Index⟧ = ⟦Index⟧R
  ℳ .Model.⟦idx⟧ n i .left = 𝒮.⟦idx⟧ n i
  ℳ .Model.⟦idx⟧ n i .right = 𝒩.⟦idx⟧ n i
  ℳ .Model.⟦idx⟧ n i .rel-mor w _ _ _ = refl
  ℳ .Model.⟦constraint⟧ = ⟦constraint⟧
  ℳ .Model.⟦∃⟧ = ⟦∃⟧

  module ℐ = Interpret ℳ

  standard : ε / ε ⊢ Bool query → S.Ex 𝔹
  standard t = ℐ.⟦ t ⟧tm tt .left tt

  normalise : ε / ε ⊢ Bool query → Query ε
  normalise t = compile (ℐ.⟦ t ⟧tm tt .right .N.mor tt)

  related : (t : ε / ε ⊢ Bool query) →
            QueryR empty (standard t) (normalise t)
  related t = compile-lemma empty _ (ℐ.⟦ t ⟧tm tt .right .N.mor tt)
                            (ℐ.⟦ t ⟧tm tt .rel-mor empty tt tt tt)


  eval-Query : ∀ {Δ} → Query Δ → Env Δ → Set
  eval-Query (constraint ϕ) η = True (eval-ConstraintExp extFunc ϕ η)
  eval-Query (ex ϕ) η = Σ[ q ∈ ℚ ] eval-Query ϕ (extend-env η q)
  eval-Query (ϕ and ψ) η = eval-Query ϕ η × eval-Query ψ η
  eval-Query (ϕ or ψ) η = eval-Query ϕ η ⊎ eval-Query ψ η

  correctness : ∀ w {x₁ x₂} →
                QueryR w x₁ x₂ →
                S.eval-Ex x₁ True ↔ eval-Query x₂ (w .env)
  correctness w (q-constraint x) = cong-True (sym x)
  correctness w (q-true {ϕ = ϕ} is-true r) =
    ↔-trans (correctness w r)
    (↔-trans or-left
            (⊎-cong (↔-trans ⊤-fst (×-cong (⊤-bool is-true) ↔-refl))
                    (↔-trans ⊥-fst (×-cong (⊥-bool (trans (sym (eval-negate extFunc ϕ (w .env))) (cong not is-true)))
                                           ↔-refl))))
  correctness w (q-false {ϕ = ϕ} is-false r) =
    ↔-trans (correctness w r)
    (↔-trans or-right
    (⊎-cong
      (↔-trans ⊥-fst (×-cong
                       (⊥-bool is-false)
                       ↔-refl))
      (↔-trans ⊤-fst (×-cong
                       (⊤-bool (trans (sym (eval-negate extFunc ϕ (w .env))) (cong not is-false)))
                       ↔-refl))))
  correctness w (q-ex x) = cong-Σ-snd (λ q → correctness (extend-w w q) (x q))
  correctness w (q-ex' q x r) =
    ↔-trans (correctness (extend-w w q) r)
            (↔-trans (known q) (cong-Σ-snd (λ q' → ×-cong (x q') ↔-refl)))
