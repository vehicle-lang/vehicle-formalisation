
open import Level using (0ℓ; suc; lift)

open import Data.Bool using (not; _∧_; _∨_; true; false)
                   renaming (Bool to 𝔹; T to True; if_then_else_ to ifᵇ_then_else_)
open import Data.Bool.Properties using (not-involutive; ∨-∧-booleanAlgebra)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product as Prod using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Rational using (ℚ; _+_; _*_; _≤ᵇ_; _≟_; 1ℚ)
open import Data.Rational.Properties using (*-identityˡ; *-comm)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; sym; cong₂; subst; module ≡-Reasoning)

open import Util using (_<ᵇ_; is-true-or-false)
open import MiniVehicle.Language.Syntax.Restriction
open import MiniVehicle.Verifiers.Syntax.Restriction
open import Util.EquiInhabited

module MiniVehicle.Verifiers.NormalisationCorrect (extFunc : ℚ → ℚ) where

open import MiniVehicle.Language.Model using (Model)
import MiniVehicle.Language.StandardSemantics as S
open import MiniVehicle.Verifiers.Normalisation as N
  using (constraint; ex; _and_; _or_)

open import Algebra.Properties.BooleanAlgebra ∨-∧-booleanAlgebra using (deMorgan₁; deMorgan₂)

open import VerifierLang.Syntax renaming (_∘_ to _∘r_)
open import VerifierLang.Semantics extFunc

------------------------------------------------------------------------------
-- Correctness of translation from ExFormula

{-
equi-conj-constraint : ∀ {Δ} (ϕ : Constraint Δ) ψ η →
                       (True (𝒞⟦ ϕ ⟧ η) × eval-PrenexFormula ψ η)
                          ⇔ eval-PrenexFormula (conj-constraint ϕ ψ) η
equi-conj-constraint ϕ (constraint x) η = True-∧
equi-conj-constraint ϕ (ex ψ) η =
  ⇔-trans
    and-comm-left
    (⇔-trans
     (cong-∃ λ q → ×-cong (cong-True (ext-evalConstraint ϕ wk-w)) ⇔-refl)
     (cong-∃ λ q →
        equi-conj-constraint (rename-Constraint succ ϕ) ψ (extend-env η q)))

equi-conj : ∀ {Δ} (ϕ : PrenexFormula Δ) ψ η →
            (eval-PrenexFormula ϕ η × eval-PrenexFormula ψ η) ⇔ eval-PrenexFormula (conj ϕ ψ) η
equi-conj (constraint ϕ) ψ η = equi-conj-constraint ϕ ψ η
equi-conj (ex ϕ) ψ η =
  ⇔-trans
   and-comm-right
   (cong-∃ λ q →
    ⇔-trans
     (×-cong ⇔-refl (ext-PrenexFormula wk-w ψ))
     (equi-conj ϕ (rename-PrenexFormula succ ψ) (extend-env η q)))

equi-disj-constraint : ∀ {Δ} (ϕ : Constraint Δ) ψ η →
                       (True (𝒞⟦ ϕ ⟧ η) ⊎ eval-PrenexFormula ψ η)
                          ⇔ eval-PrenexFormula (disj-constraint ϕ ψ) η
equi-disj-constraint ϕ (constraint x) η = True-∨
equi-disj-constraint ϕ (ex ψ) η =
  ⇔-trans
   (or-comm-right 1ℚ)
   (cong-∃
    λ q → ⇔-trans
           (⊎-cong (cong-True (ext-evalConstraint ϕ wk-w)) ⇔-refl)
           (equi-disj-constraint (rename-Constraint succ ϕ) ψ (extend-env η q)))

equi-disj : ∀ {Δ} (ϕ : PrenexFormula Δ) ψ η →
            (eval-PrenexFormula ϕ η ⊎ eval-PrenexFormula ψ η) ⇔ eval-PrenexFormula (disj ϕ ψ) η
equi-disj (constraint ϕ) ψ η = equi-disj-constraint ϕ ψ η
equi-disj (ex ϕ) ψ η =
  ⇔-trans (or-comm-left 1ℚ)
   (cong-∃ λ q →
    ⇔-trans
     (⊎-cong ⇔-refl (ext-PrenexFormula wk-w ψ))
     (equi-disj ϕ (rename-PrenexFormula succ ψ) (extend-env η q)))
-}


eval-ExFormula : ∀ {Δ} → N.ExFormula Δ → Env Δ → Set
eval-ExFormula (constraint ϕ) η = True (𝒞⟦ ϕ ⟧ η)
eval-ExFormula (ex ϕ) η = Σ[ q ∈ ℚ ] eval-ExFormula ϕ (extend-env η q)
eval-ExFormula (ϕ and ψ) η = eval-ExFormula ϕ η × eval-ExFormula ψ η
eval-ExFormula (ϕ or ψ) η = eval-ExFormula ϕ η ⊎ eval-ExFormula ψ η

eval-BoolExpr : ∀ {Δ} → N.BoolExpr Δ → Env Δ → 𝔹
eval-BoolExpr (constraint ϕ) η = 𝒞⟦ ϕ ⟧ η
eval-BoolExpr (ϕ and ψ) η = eval-BoolExpr ϕ η ∧ eval-BoolExpr ψ η
eval-BoolExpr (ϕ or ψ) η = eval-BoolExpr ϕ η ∨ eval-BoolExpr ψ η

eval-negate : ∀ {Δ} (p : Constraint Δ) η → not (𝒞⟦ p ⟧ η) ≡ 𝒞⟦ negate p ⟧ η
eval-negate (x `≤` x₁) η = refl
eval-negate (x `<` x₁) η = not-involutive _
eval-negate (x `=` x₁) η = refl
eval-negate (x `≠` x₁) η = not-involutive _
eval-negate (x₁ `=`f x₂) η = refl
eval-negate (x₁ `≠`f x₂) η = not-involutive _

eval-negate-BoolExpr : ∀ {Δ} (p : N.BoolExpr Δ) η →
                       not (eval-BoolExpr p η) ≡ eval-BoolExpr (N.negate-BoolExpr p) η
eval-negate-BoolExpr (constraint p) η rewrite sym (eval-negate p η) = refl
eval-negate-BoolExpr (p and q)      η rewrite sym (eval-negate-BoolExpr p η)
                         rewrite sym (eval-negate-BoolExpr q η) =
                            deMorgan₁ (eval-BoolExpr p η) (eval-BoolExpr q η)
eval-negate-BoolExpr (p or q)       η rewrite sym (eval-negate-BoolExpr p η)
                         rewrite sym (eval-negate-BoolExpr q η) =
                            deMorgan₂ (eval-BoolExpr p η) (eval-BoolExpr q η)
{-
toPrenexForm-ok : ∀ {Δ} (ϕ : N.ExFormula Δ) η →
             eval-ExFormula ϕ η ⇔ eval-PrenexFormula (N.toPrenexForm ϕ) η
toPrenexForm-ok (constraint x) η = ⇔-refl
toPrenexForm-ok (ex ϕ) η = cong-∃ λ q → toPrenexForm-ok ϕ (extend-env η q)
toPrenexForm-ok (ϕ and ψ) η =
  ⇔-trans (×-cong (toPrenexForm-ok ϕ η) (toPrenexForm-ok ψ η))
            (equi-conj (N.toPrenexForm ϕ) (N.toPrenexForm ψ) η)
toPrenexForm-ok (ϕ or ψ) η =
  ⇔-trans (⊎-cong (toPrenexForm-ok ϕ η) (toPrenexForm-ok ψ η))
            (equi-disj (N.toPrenexForm ϕ) (N.toPrenexForm ψ) η)
-}
------------------------------------------------------------------------------
-- Our category of related interpretations

module 𝒩 = Model N.ℳ
module 𝒮 = Model S.ℳ

record ⟦Type⟧ : Set (suc 0ℓ) where
  field
    Left  : 𝒮.⟦Type⟧
    Right : 𝒩.⟦Type⟧
    rel   : (w : World) → Left → Right .N.Carrier (w .ctxt) → Set
    ext   : ∀ {w w'} (ρ : w' ⇒w w) a b → rel w a b → rel w' a (Right .N.rename (ρ .ren) b)
open ⟦Type⟧

infixr 20 _==>_
record _==>_ (X Y : ⟦Type⟧) : Set where
  field
    left    : X .Left 𝒮.==> Y .Left
    right   : X .Right 𝒩.==> Y .Right
    rel-mor : ∀ w lx rx → X .rel w lx rx → Y .rel w (left lx) (right .N.mor rx)
open _==>_

------------------------------------------------------------------------------
-- Composition

_∘_ : ∀ {X Y Z} → (Y ==> Z) → (X ==> Y) → (X ==> Z)
(f ∘ g) .left  = f .left  𝒮.∘ g .left
(f ∘ g) .right = f .right 𝒩.∘ g .right
(f ∘ g) .rel-mor w x₁ x₂ r-x₁x₂ = f .rel-mor w _ _ (g .rel-mor w _ _ r-x₁x₂)

⟦id⟧ : ∀ {X} → X ==> X
⟦id⟧ .left x = x
⟦id⟧ .right = 𝒩.⟦id⟧
⟦id⟧ .rel-mor w x₁ x₂ r = r

------------------------------------------------------------------------------
-- Sets
Flat : Set → ⟦Type⟧
Flat X .Left = X
Flat X .Right = N.Flat X
Flat X .rel w x₁ x₂ = x₁ ≡ x₂
Flat X .ext ρ x₁ x₂ eq = eq

elem : ∀ {A X} → A → X ==> Flat A
elem a .left = 𝒮.elem a
elem a .right = 𝒩.elem a
elem a .rel-mor w _ _ _ = refl

Flat-map : ∀ {A B} → (A → B) → Flat A ==> Flat B
Flat-map f .left = f
Flat-map f .right = N.Flat-map f
Flat-map f .rel-mor w lx rx = cong f

------------------------------------------------------------------------------
-- Products

infixr 2 _⟦×⟧_

_⟦×⟧_ : ⟦Type⟧ → ⟦Type⟧ → ⟦Type⟧
(X ⟦×⟧ Y) .Left = X .Left 𝒮.⟦×⟧ Y .Left
(X ⟦×⟧ Y) .Right = X .Right 𝒩.⟦×⟧ Y .Right
(X ⟦×⟧ Y) .rel w (x , y) (x' , y') = X .rel w x x' × Y .rel w y y'
(X ⟦×⟧ Y) .ext ρ (x , y) (x' , y') (r₁ , r₂) =
  (X .ext ρ x x' r₁) , (Y .ext ρ y y' r₂)

⟨_,_⟩R : ∀ {X Y Z} → (X ==> Y) → (X ==> Z) → (X ==> (Y ⟦×⟧ Z))
⟨ f , g ⟩R .left = 𝒮.⟨ f .left , g .left ⟩
⟨ f , g ⟩R .right = 𝒩.⟨ f .right , g .right ⟩
⟨ f , g ⟩R .rel-mor w x₁ x₂ r-x₁x₂ =
  f .rel-mor w x₁ x₂ r-x₁x₂ ,
  g .rel-mor w x₁ x₂ r-x₁x₂

⟦proj₁⟧ : ∀ {X Y} → (X ⟦×⟧ Y) ==> X
⟦proj₁⟧ .left = proj₁
⟦proj₁⟧ .right = 𝒩.⟦proj₁⟧
⟦proj₁⟧ .rel-mor w _ _ r = r .proj₁

⟦proj₂⟧ : ∀ {X Y} → (X ⟦×⟧ Y) ==> Y
⟦proj₂⟧ .left = proj₂
⟦proj₂⟧ .right = 𝒩.⟦proj₂⟧
⟦proj₂⟧ .rel-mor w _ _ r = r .proj₂

------------------------------------------------------------------------------
-- Functions and Universal Quantification

_⟦⇒⟧_ : ⟦Type⟧ → ⟦Type⟧ → ⟦Type⟧
(X ⟦⇒⟧ Y) .Left = X .Left 𝒮.⟦⇒⟧ Y .Left
(X ⟦⇒⟧ Y) .Right = X .Right 𝒩.⟦⇒⟧ Y .Right
(X ⟦⇒⟧ Y) .rel w f g =
  ∀ w' (ρ : w' ⇒w w) x y →
     X .rel w' x y →
     Y .rel w' (f x) (g (w' .ctxt) (ρ .ren) y)
(X ⟦⇒⟧ Y) .ext ρ f g r =
  λ w'' ρ' x y → r w'' (ρ ∘w ρ') x y

⟦Λ⟧ : ∀ {X Y Z} → ((X ⟦×⟧ Y) ==> Z) → (X ==> (Y ⟦⇒⟧ Z))
⟦Λ⟧ {X} f .left = 𝒮.⟦Λ⟧ (f .left)
⟦Λ⟧ {X} f .right = 𝒩.⟦Λ⟧ (f .right)
⟦Λ⟧ {X} f .rel-mor w x₁ x₂ r-x₁x₂ w' ρ y₁ y₂ r-y₁y₂ =
  f .rel-mor w' (x₁ , y₁)
                (X .Right .N.rename (ρ .ren) x₂ , y₂)
                (X .ext ρ x₁ x₂ r-x₁x₂ , r-y₁y₂)

⟦eval⟧ : ∀ {X Y} → ((X ⟦⇒⟧ Y) ⟦×⟧ X) ==> Y
⟦eval⟧ .left = 𝒮.⟦eval⟧
⟦eval⟧ .right = 𝒩.⟦eval⟧
⟦eval⟧ .rel-mor w (f₁ , x₁) (f₂ , x₂) (r-f₁f₂ , r-x₁x₂) =
  r-f₁f₂ w id-w x₁ x₂ r-x₁x₂

⟦∀⟧ : ∀ {I : Set} → (I → ⟦Type⟧) → ⟦Type⟧
⟦∀⟧ A .Left = 𝒮.⟦∀⟧ (λ n → A n .Left)
⟦∀⟧ A .Right = 𝒩.⟦∀⟧ (λ n → A n .Right)
⟦∀⟧ A .rel w x y = ∀ n → A n .rel w (x n) (y n)
⟦∀⟧ A .ext ρ x y r n = A n .ext ρ (x n) (y n) (r n)

⟦∀-intro⟧ : ∀ {I X A} → (∀ (n : I) → X ==> A n) → X ==> ⟦∀⟧ A
⟦∀-intro⟧ f .left = 𝒮.⟦∀-intro⟧ (λ n → f n .left)
⟦∀-intro⟧ f .right = 𝒩.⟦∀-intro⟧ (λ n → f n .right)
⟦∀-intro⟧ f .rel-mor w x₁ x₂ r n = f n .rel-mor w x₁ x₂ r

⟦∀-elim⟧ : ∀ {I A} (n : I) → ⟦∀⟧ A ==> A n
⟦∀-elim⟧ n .left = 𝒮.⟦∀-elim⟧ n
⟦∀-elim⟧ n .right = 𝒩.⟦∀-elim⟧ n
⟦∀-elim⟧ n .rel-mor w f₁ f₂ r = r n

------------------------------------------------------------------------------
-- Numbers, and linear expressions
⟦Num⟧ : LinearityVal → ⟦Type⟧
⟦Num⟧ p .Left = 𝒮.⟦Num⟧ tt
⟦Num⟧ p .Right = 𝒩.⟦Num⟧ p
⟦Num⟧ const .rel _ q₁ q₂ = q₁ ≡ q₂
⟦Num⟧ const .ext _ _ _ eq = eq
⟦Num⟧ linear .rel w x exp = x ≡ ℰ⟦ exp ⟧ (w .env)
⟦Num⟧ linear .ext ρ x exp eq = trans eq (ext-evalLinExp exp ρ)
⟦Num⟧ nonlinear .rel w x tt = ⊤
⟦Num⟧ nonlinear .ext _ _ _ _ = tt

⟦const⟧ : ∀ {l} → ℚ → Flat (NumConstRel l) ==> ⟦Num⟧ l
⟦const⟧ q .left _ = q
⟦const⟧ q .right = 𝒩.⟦const⟧ q
⟦const⟧ q .rel-mor w const const _ = refl

⟦add⟧ : ∀ {l₁ l₂ l₃} → (Flat (MaxLinRel l₁ l₂ l₃) ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Num⟧ l₃
⟦add⟧ .left = λ {(_ , (u , v)) → 𝒮.⟦add⟧ (_ , (u , v))}
⟦add⟧ .right = 𝒩.⟦add⟧
⟦add⟧ .rel-mor w (const-const   , x₁ , y₁) (_ , x₂ , y₂) (refl , x₁₂ , y₁₂) =
  cong₂ _+_ x₁₂ y₁₂
⟦add⟧ .rel-mor w (const-linear  , x₁ , y₁) (_ , x₂ , y₂) (refl , x₁₂ , y₁₂) =
  cong₂ _+_ x₁₂ y₁₂
⟦add⟧ .rel-mor w (linear-const  , x₁ , y₁) (_ , x₂ , y₂) (refl , x₁₂ , y₁₂) =
  cong₂ _+_ x₁₂ y₁₂
⟦add⟧ .rel-mor w (linear-linear , x₁ , y₁) (_ , x₂ , y₂) (refl , x₁₂ , y₁₂) =
  cong₂ _+_ x₁₂ y₁₂

⟦mul⟧ : ∀ {l₁ l₂ l₃} → (Flat (MulLinRel l₁ l₂ l₃) ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Num⟧ l₃
⟦mul⟧ .left = λ {(x , (u , v)) → 𝒮.⟦mul⟧ (_ , (u , v))}
⟦mul⟧ .right = 𝒩.⟦mul⟧
⟦mul⟧ .rel-mor w (const-const  , x₁ , y₁) (_ , x₂ , y₂) (refl , x₁₂ , y₁₂) =
  cong₂ _*_ x₁₂ y₁₂
⟦mul⟧ .rel-mor w (const-linear , x₁ , y₁) (_ , x₂ , y₂) (refl , x₁₂ , y₁₂) =
  trans (cong₂ _*_ x₁₂ y₁₂) (eval-⊛ x₂ y₂ (w .env))
⟦mul⟧ .rel-mor w (linear-const , x₁ , y₁) (_ , x₂ , y₂) (refl , x₁₂ , y₁₂) =
  trans (cong₂ _*_ x₁₂ y₁₂)
    (trans (*-comm (ℰ⟦ x₂ ⟧ (w .env)) y₂) (eval-⊛ y₂ x₂ (w .env)))

------------------------------------------------------------------------------
-- Booleans and constraints

data ExFormulaR : ∀ w → S.Quant 𝔹 → N.ExFormula (w .ctxt) → Set where
  q-constraint : ∀ {w b ϕ} →
                 𝒞⟦ ϕ ⟧ (w .env) ≡ b →
                 ExFormulaR w (S.return b) (constraint ϕ)
  q-true       : ∀ {w x ϕ ψ₁ ψ₂} →
                 𝒞⟦ ϕ ⟧ (w .env) ≡ true →
                 ExFormulaR w x ψ₁ →
                 ExFormulaR w x ((constraint ϕ and ψ₁) or (constraint (negate ϕ) and ψ₂))
  q-false      : ∀ {w x ϕ ψ₁ ψ₂} →
                 𝒞⟦ ϕ ⟧ (w .env) ≡ false →
                 ExFormulaR w x ψ₂ →
                 ExFormulaR w x ((constraint ϕ and ψ₁) or (constraint (negate ϕ) and ψ₂))
  q-ex         : ∀ {w k ϕ} →
                 (∀ q → ExFormulaR (extend-w w q) (k q) ϕ) →
                 ExFormulaR w (S.ex k) (ex ϕ)
  q-ex'        : ∀ {w x ϕ ψ} q →
                 (∀ q' → (q' ≡ q) ⇔ True (𝒞⟦ ϕ ⟧ (extend-env (w .env) q'))) →
                 ExFormulaR (extend-w w q) x ψ →
                 ExFormulaR w x (ex (constraint ϕ and ψ))
  q-and        : ∀ {w ϕ₁ ϕ₂ ψ₁ ψ₂ } →
                 ExFormulaR w ϕ₁ ψ₁ →
                 ExFormulaR w ϕ₂ ψ₂ →
                 ExFormulaR w (ϕ₁ S.and ϕ₂) (ψ₁ and ψ₂)
  q-or         : ∀ {w ϕ₁ ϕ₂ ψ₁ ψ₂ } →
                 ExFormulaR w ϕ₁ ψ₁ →
                 ExFormulaR w ϕ₂ ψ₂ →
                 ExFormulaR w (ϕ₁ S.or ϕ₂) (ψ₁ or ψ₂)


data BoolExprR : ∀ w → S.Quant 𝔹 → N.BoolExpr (w .ctxt) → Set where
  q-constraint : ∀ {w b ϕ} →
                 𝒞⟦ ϕ ⟧ (w .env) ≡ b →
                 BoolExprR w (S.return b) (constraint ϕ)
  q-and        : ∀ {w ϕ₁ ϕ₂ ψ₁ ψ₂ } →
                 BoolExprR w ϕ₁ ψ₁ →
                 BoolExprR w ϕ₂ ψ₂ →
                 BoolExprR w (ϕ₁ S.and ϕ₂) (ψ₁ and ψ₂)
  q-or         : ∀ {w ϕ₁ ϕ₂ ψ₁ ψ₂ } →
                 BoolExprR w ϕ₁ ψ₁ →
                 BoolExprR w ϕ₂ ψ₂ →
                 BoolExprR w (ϕ₁ S.or ϕ₂) (ψ₁ or ψ₂)

ext-ExFormula : ∀ {w₁ w₂} (ρ : w₂ ⇒w w₁) x₁ x₂ →
            ExFormulaR w₁ x₁ x₂ → ExFormulaR w₂ x₁ (N.rename-ExFormula (ρ .ren) x₂)
ext-ExFormula ρ _ _ (q-constraint {ϕ = ϕ} x) =
  q-constraint (trans (sym (ext-evalConstraint ϕ ρ)) x)
ext-ExFormula ρ _ _ (q-true {ϕ = ϕ} is-true r) rewrite rename-negate (ρ .ren) ϕ =
  q-true (trans (sym (ext-evalConstraint ϕ ρ)) is-true) (ext-ExFormula ρ _ _ r)
ext-ExFormula ρ _ _ (q-false {ϕ = ϕ} is-false r) rewrite rename-negate (ρ .ren) ϕ =
  q-false (trans (sym (ext-evalConstraint ϕ ρ)) is-false) (ext-ExFormula ρ _ _ r)
ext-ExFormula ρ _ _ (q-ex r) = q-ex λ q → ext-ExFormula (under-w ρ) _ _ (r q)
ext-ExFormula ρ _ _ (q-ex' {ϕ = ϕ} q uniq r) =
  q-ex' q (λ q' → ⇔-trans (uniq q') (cong-True (ext-evalConstraint ϕ (under-w ρ))))
        (ext-ExFormula (under-w ρ) _ _ r)
ext-ExFormula ρ _ _ (q-and r₁ r₂) = q-and (ext-ExFormula ρ _ _ r₁) (ext-ExFormula ρ _ _ r₂)
ext-ExFormula ρ _ _ (q-or r₁ r₂) = q-or (ext-ExFormula ρ _ _ r₁) (ext-ExFormula ρ _ _ r₂)

ext-evalBoolExpr : 
  ∀ {w₁ w₂} ϕ (ρ : w₂ ⇒w w₁) →
    eval-BoolExpr ϕ (w₁ .env) ≡ eval-BoolExpr (N.rename-BoolExpr (ρ .ren) ϕ) (w₂ .env)
ext-evalBoolExpr (constraint ϕ) ρ rewrite ext-evalConstraint ϕ ρ = refl
ext-evalBoolExpr (ϕ₁ and ϕ₂)    ρ rewrite ext-evalBoolExpr ϕ₁ ρ | ext-evalBoolExpr ϕ₂ ρ = refl
ext-evalBoolExpr (ϕ₁ or  ϕ₂)    ρ rewrite ext-evalBoolExpr ϕ₁ ρ | ext-evalBoolExpr ϕ₂ ρ = refl

⟦Bool⟧ : LinearityVal × PolarityVal → ⟦Type⟧
⟦Bool⟧ (l , p) .Left = 𝒮.⟦Bool⟧ p
⟦Bool⟧ (l , p) .Right = 𝒩.⟦Bool⟧ (l , p)
⟦Bool⟧ (l , U) .rel w b ϕ = b ≡ eval-BoolExpr ϕ (w .env)
⟦Bool⟧ (l , U) .ext ρ b ϕ eq = trans eq (ext-evalBoolExpr ϕ ρ)
⟦Bool⟧ (l , Ex) .rel = ExFormulaR
⟦Bool⟧ (l , Ex) .ext = ext-ExFormula

⟦≤⟧ : ∀ {l₁ l₂ l₃} → (Flat (CompRes l₁ l₂ l₃) ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Bool⟧ l₃
⟦≤⟧ .left = λ { (compRes _ , u) → 𝒮.⟦≤⟧ (U , u) }
⟦≤⟧ .right = 𝒩.⟦≤⟧
⟦≤⟧ .rel-mor w (compRes const-const   , x₁ , y₁) (_ , x₂ , y₂) (refl , x₁₂ , y₁₂) =
  cong₂ _≤ᵇ_ x₁₂ y₁₂
⟦≤⟧ .rel-mor w (compRes const-linear  , x₁ , y₁) (_ , x₂ , y₂) (refl , x₁₂ , y₁₂) =
  cong₂ _≤ᵇ_ x₁₂ y₁₂
⟦≤⟧ .rel-mor w (compRes linear-const  , x₁ , y₁) (_ , x₂ , y₂) (refl , x₁₂ , y₁₂) =
  cong₂ _≤ᵇ_ x₁₂ y₁₂
⟦≤⟧ .rel-mor w (compRes linear-linear , x₁ , y₁) (_ , x₂ , y₂) (refl , x₁₂ , y₁₂) =
  cong₂ _≤ᵇ_ x₁₂ y₁₂

⟦<⟧ : ∀ {l₁ l₂ l₃} → (Flat (CompRes l₁ l₂ l₃) ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Bool⟧ l₃
⟦<⟧ .left = λ { (compRes _ , u) → 𝒮.⟦<⟧ (U , u) }
⟦<⟧ .right = 𝒩.⟦<⟧
⟦<⟧ .rel-mor w (compRes const-const   , x₁ , y₁) (_ , x₂ , y₂) (refl , x₁₂ , y₁₂) =
  cong₂ _<ᵇ_ x₁₂ y₁₂
⟦<⟧ .rel-mor w (compRes const-linear  , x₁ , y₁) (_ , x₂ , y₂) (refl , x₁₂ , y₁₂) =
  cong₂ _<ᵇ_ x₁₂ y₁₂
⟦<⟧ .rel-mor w (compRes linear-const  , x₁ , y₁) (_ , x₂ , y₂) (refl , x₁₂ , y₁₂) =
  cong₂ _<ᵇ_ x₁₂ y₁₂
⟦<⟧ .rel-mor w (compRes linear-linear , x₁ , y₁) (_ , x₂ , y₂) (refl , x₁₂ , y₁₂) =
  cong₂ _<ᵇ_ x₁₂ y₁₂

⟦and⟧ : ∀ {l₁ l₂ l₃} →
          (Flat (MaxBoolRes l₁ l₂ l₃) ⟦×⟧
            (⟦Bool⟧ l₁ ⟦×⟧ ⟦Bool⟧ l₂)) ==> ⟦Bool⟧ l₃
⟦and⟧ .left = λ { (maxBoolRes _ v , x) → 𝒮.⟦and⟧ (v , x)}
⟦and⟧ .right = 𝒩.⟦and⟧
⟦and⟧ .rel-mor w (maxBoolRes _ U-U , _) (maxBoolRes _ U-U , _) (eq , x₁₂ , y₁₂) =
  cong₂ _∧_ x₁₂ y₁₂
⟦and⟧ .rel-mor w (maxBoolRes _ U-Ex , _) (maxBoolRes _ U-Ex , _) (_ , x₁₂ , y₁₂) =
  q-and {!!} {!!} --q-and (q-constraint (sym x₁₂)) y₁₂
⟦and⟧ .rel-mor w (maxBoolRes _ Ex-U , _) (maxBoolRes _ Ex-U , _) (_ , x₁₂ , y₁₂) =
  {!!} --q-and x₁₂ (q-constraint (sym y₁₂))
⟦and⟧ .rel-mor w (maxBoolRes _ Ex-Ex , _) (maxBoolRes _ Ex-Ex , _) (_ ,  x₁₂ , y₁₂) =
  q-and x₁₂ y₁₂

⟦or⟧ : ∀ {l₁ l₂ l₃} →
          (Flat (MaxBoolRes l₁ l₂ l₃) ⟦×⟧
            (⟦Bool⟧ l₁ ⟦×⟧ ⟦Bool⟧ l₂)) ==> ⟦Bool⟧ l₃
⟦or⟧ .left = λ { (maxBoolRes _ v , x) → 𝒮.⟦or⟧ (v , x)}
⟦or⟧ .right = 𝒩.⟦or⟧
⟦or⟧ .rel-mor w (maxBoolRes _ U-U , _) (maxBoolRes _ U-U , _) (_ , x₁₂ , y₁₂) =
  cong₂ _∨_ x₁₂ y₁₂
⟦or⟧ .rel-mor w (maxBoolRes _  U-Ex , _) (maxBoolRes _ U-Ex , _) (_ , x₁₂ , y₁₂) =
  {!!} --q-or (q-constraint (sym x₁₂)) y₁₂
⟦or⟧ .rel-mor w (maxBoolRes _  Ex-U , _) (maxBoolRes _ Ex-U , _) (_ , x₁₂ , y₁₂) =
  {!!} --q-or x₁₂ (q-constraint (sym y₁₂))
⟦or⟧ .rel-mor w (maxBoolRes _  Ex-Ex , _) (maxBoolRes _ Ex-Ex , _) (_ , x₁₂ , y₁₂) =
  q-or x₁₂ y₁₂

⟦not⟧ : ∀ {p₁ p₂} → (Flat (NotRes p₁ p₂) ⟦×⟧ ⟦Bool⟧ p₁) ==> ⟦Bool⟧ p₂
⟦not⟧ .left = λ { (notRes v , x) → 𝒮.⟦not⟧ (v , x)}
⟦not⟧ .right = 𝒩.⟦not⟧
⟦not⟧ .rel-mor w (notRes U , x₁) (_ , x₂) (refl , x₁₂) =
  trans (cong not x₁₂) {!!} --(eval-negate x₂ (w .env))

------------------------------------------------------------------------------
module _ (X : ⟦Type⟧) where

  LetLiftR : (w : World) → X .Left → N.LetLift (X .Right .N.Carrier) (w .ctxt) → Set
  LetLiftR w a (N.return b) = X .rel w a b
  LetLiftR w a (N.if c k₁ k₂) =
    ifᵇ {!!} --(𝒞⟦ c ⟧ (w .env))
     then LetLiftR w a k₁
     else LetLiftR w a k₂
  LetLiftR w a (N.let-linexp e k) =
    LetLiftR (extend-w w (ℰ⟦ e ⟧ (w .env))) a k
  LetLiftR w a (N.let-funexp x k) =
    LetLiftR (extend-w w (extFunc (w .env x))) a k

  ext-lift : ∀ {w₁ w₂} (ρ : w₂ ⇒w w₁) la lb →
             LetLiftR w₁ la lb →
             LetLiftR w₂ la (N.rename-lift (X .Right .N.rename) (ρ .ren) lb)
  ext-lift ρ a (N.return b) = X .ext ρ a b
  ext-lift {w₁} ρ a (N.if c tru fal) = {!!}
  {-
  rewrite sym (ext-evalConstraint c ρ) with 𝒞⟦ c ⟧ (w₁ .env)
  ... | false = ext-lift ρ a fal
  ... | true  = ext-lift ρ a tru
  -}
  ext-lift ρ a (N.let-linexp x lb) =
    ext-lift (under-w' (sym (ext-evalLinExp x ρ)) ρ) a lb
  ext-lift ρ a (N.let-funexp x lb) =
    ext-lift (under-w' (cong extFunc (ρ .presv x)) ρ) a lb

  LiftMR : ⟦Type⟧
  LiftMR .Left = 𝒮.Mon (X .Left)
  LiftMR .Right = 𝒩.Mon (X .Right)
  LiftMR .rel = LetLiftR
  LiftMR .ext = ext-lift

let-bindR : ∀ {X Y} w x y →
  (f : X .Left → Y .Left)
  (g : (X .Right .N.Carrier ⇒ₖ N.LetLift (Y .Right .N.Carrier)) (w .ctxt)) →
  LetLiftR X w x y →
  (∀ w' (ρ : w' ⇒w w) a b → X .rel w' a b → LetLiftR Y w' (f a) (g (w' .ctxt) (ρ .ren) b)) →
  LetLiftR Y w (f x) (N.bind-let y g)
let-bindR w x₁ (N.return x₂) f g r-x₁x₂ r-fg = r-fg w id-w x₁ x₂ r-x₁x₂
let-bindR w x₁ (N.if c x₂₁ x₂₂) f g r-x₁x₂ r-fg = {!!}
{-
with 𝒞⟦ c ⟧ (w .env)
... | true = let-bindR w x₁ x₂₁ f g r-x₁x₂ r-fg
... | false = let-bindR w x₁ x₂₂ f g r-x₁x₂ r-fg
-}
let-bindR w x₁ (N.let-linexp e x₂) f g r-x₁x₂ r-fg =
  let-bindR (extend-w w (ℰ⟦ e ⟧ (w .env)))
     x₁ x₂ f (λ Δ' ρ → g Δ' (wk-r ∘r ρ))
     r-x₁x₂
     λ w' ρ → r-fg w' (wk-w ∘w ρ)
let-bindR w x₁ (N.let-funexp v x₂) f g r-x₁x₂ r-fg =
  let-bindR (extend-w w (extFunc (w .env v)))
     x₁ x₂ f (λ Δ' ρ → g Δ' (wk-r ∘r ρ))
     r-x₁x₂
     λ w' ρ → r-fg w' (wk-w ∘w ρ)

⟦return⟧ : ∀ {X} → X ==> LiftMR X
⟦return⟧ .left = 𝒮.⟦return⟧
⟦return⟧ .right = 𝒩.⟦return⟧
⟦return⟧ .rel-mor w x₁ x₂ r-x₁x₂ = r-x₁x₂

⟦if⟧ : ∀ {X b} → ((LiftMR X ⟦×⟧ LiftMR X) ⟦×⟧ (Flat (IfRes b) ⟦×⟧ (⟦Bool⟧ b))) ==> LiftMR X
⟦if⟧ .left = λ { (a , ifRes u , s) → 𝒮.⟦if⟧ (a , U , s) }
⟦if⟧ .right = 𝒩.⟦if⟧
⟦if⟧ .rel-mor w ((tr₁ , fa₁) , (ifRes _ , false)) ((tr₂ , fa₂) , (ifRes _ , ϕ)) ((tr₁-tr₂ , fa₁-fa₂) , (_ , eq)) rewrite sym eq = fa₁-fa₂
⟦if⟧ .rel-mor w ((tr₁ , fa₁) , (ifRes _ , true)) ((tr₂ , fa₂) , (ifRes _ , ϕ)) ((tr₁-tr₂ , fa₁-fa₂) , (_ , eq)) rewrite sym eq = tr₁-tr₂

extendR : ∀ {X Y Z} → ((X ⟦×⟧ Y) ==> LiftMR Z) → (X ⟦×⟧ LiftMR Y) ==> LiftMR Z
extendR f .left = 𝒮.⟦extend⟧ (f .left)
extendR f .right = 𝒩.⟦extend⟧ (f .right)
extendR {X} f .rel-mor w (x₁ , ly₁) (x₂ , ly₂) (x₁x₂ , ly₁-ly₂) =
  let-bindR w ly₁ ly₂
    (λ y → f .left (x₁ , y))
    (λ Δ' ρ y → f .right .N.mor (X .Right .N.rename ρ x₂ , y))
    ly₁-ly₂
    λ w' ρ y₁ y₂ y₁y₂ →
      f .rel-mor w' (x₁ , y₁) (X .Right .N.rename (ρ .ren) x₂ , y₂) (X .ext ρ x₁ x₂ x₁x₂ , y₁y₂)

compile-lemma : ∀ l w x₁ x₂ → LetLiftR (⟦Bool⟧ (l , Ex)) w x₁ x₂ → ExFormulaR w x₁ (N.compile x₂)
compile-lemma l w x₁ (N.return x) r = r
compile-lemma l w x₁ (N.if ϕ tr fa) r = {!!}
{-
with is-true-or-false (𝒞⟦ ϕ ⟧ (w .env))
... | inj₁ is-true =
       q-true is-true (compile-lemma l w _ tr (subst (λ □ → ifᵇ □ then _ else _) is-true r))
... | inj₂ is-false =
       q-false is-false (compile-lemma l w _ fa (subst (λ □ → ifᵇ □ then _ else _) is-false r))
-}
compile-lemma l w x₁ (N.let-linexp e k) r =
  q-ex' q
        (λ q' →
          ⇔-trans (eq-cong
                    (sym (*-identityˡ q'))
                    (ext-evalLinExp e wk-w))
           (⇔-sym (does-cong (1ℚ * q' ≟
                               ℰ⟦ rename-LinExp succ e ⟧ (extend-env (w .env) q')))))
        (compile-lemma l (extend-w w q) x₁ k r)
  where q : ℚ
        q = ℰ⟦ e ⟧ (w .env)
compile-lemma l w x₁ (N.let-funexp x k) r =
  q-ex' q
        (λ q' → ⇔-sym (does-cong (q' ≟ extFunc (w .env x))))
        (compile-lemma l (extend-w w q) x₁ k r)
  where q : ℚ
        q = extFunc (w .env x)

⟦∃⟧ : ∀ {p₁ p₂ l} →
     (Flat (QuantRes l p₁ p₂) ⟦×⟧ (⟦Num⟧ l ⟦⇒⟧ LiftMR (⟦Bool⟧ p₁))) ==> ⟦Bool⟧ p₂
⟦∃⟧ .left = λ { (quantRes u , v) → 𝒮.⟦∃⟧ (u , v) }
⟦∃⟧ {l = l} .right = 𝒩.⟦∃⟧ {l = l}
⟦∃⟧ {l = l} .rel-mor w (quantRes U  , f₁) (quantRes U , f₂) (refl , r) =
  q-ex (λ q → compile-lemma l (extend-w w q)
                   (S.return (f₁ q))
                   (N.bind-let (f₂ (w .ctxt ,∙) succ (1ℚ `*`var zero))
                     {!!}) -- (λ Δ' ρ ϕ → N.return (constraint ϕ)))
                   (let-bindR (extend-w w q)
                     (f₁ q)
                     (f₂ (w .ctxt ,∙) succ (1ℚ `*`var zero))
                     S.return
                     _
                     (r (extend-w w q) wk-w q (1ℚ `*`var zero) (sym (*-identityˡ q)))
                     λ w' ρ a b x → {!!})) --q-constraint (sym x)))
⟦∃⟧ {l = l} .rel-mor w (quantRes Ex , f₁) (quantRes Ex , f₂) (refl , r) =
  q-ex λ q → compile-lemma l (extend-w w q) (f₁ q) (f₂ (w .ctxt ,∙) succ (1ℚ `*`var zero))
               (r (extend-w w q) wk-w q (1ℚ `*`var zero) (sym (*-identityˡ q)))

ExFormulaR-ok : ∀ w {x₁ x₂} →
              ExFormulaR w x₁ x₂ →
              S.eval-Quant x₁ True ⇔ eval-ExFormula x₂ (w .env)
ExFormulaR-ok w (q-constraint x) = cong-True (sym x)
ExFormulaR-ok w (q-true {ϕ = ϕ} is-true r) =
  ⇔-trans (ExFormulaR-ok w r)
  (⇔-trans or-left
          (⊎-cong (⇔-trans ⊤-fst (×-cong (⊤-bool is-true) ⇔-refl))
                  (⇔-trans ⊥-fst (×-cong (⊥-bool (trans (sym (eval-negate ϕ (w .env))) (cong not is-true)))
                                         ⇔-refl))))
ExFormulaR-ok w (q-false {ϕ = ϕ} is-false r) =
  ⇔-trans (ExFormulaR-ok w r)
  (⇔-trans or-right
  (⊎-cong
    (⇔-trans ⊥-fst (×-cong
                     (⊥-bool is-false)
                     ⇔-refl))
    (⇔-trans ⊤-fst (×-cong
                     (⊤-bool (trans (sym (eval-negate ϕ (w .env))) (cong not is-false)))
                     ⇔-refl))))
ExFormulaR-ok w (q-ex x) = cong-∃ (λ q → ExFormulaR-ok (extend-w w q) (x q))
ExFormulaR-ok w (q-ex' q x r) =
  ⇔-trans (ExFormulaR-ok (extend-w w q) r)
           (⇔-trans (known q) (cong-∃ (λ q' → ×-cong (x q') ⇔-refl)))
ExFormulaR-ok w (q-and r₁ r₂) = ×-cong (ExFormulaR-ok w r₁) (ExFormulaR-ok w r₂)
ExFormulaR-ok w (q-or r₁ r₂) = ⊎-cong (ExFormulaR-ok w r₁) (ExFormulaR-ok w r₂)

ℳ : Model verifierRestriction (suc 0ℓ) 0ℓ
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
ℳ .Model.Mon = LiftMR
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
ℳ .Model.⟦if⟧ = ⟦if⟧
ℳ .Model.⟦∃⟧ = ⟦∃⟧

------------------------------------------------------------------------------
open import MiniVehicle.Language.Syntax verifierRestriction hiding (_⇒ᵣ_; under)
import MiniVehicle.Language.Interpretation verifierRestriction ℳ as ℐ

standard : NetworkSpecification linear (linear , Ex) → Set
standard t = S.eval-Quant (ℐ.⟦ t ⟧tm (lift tt) .left (tt , extFunc)) True

normalise : NetworkSpecification linear (linear , Ex) → QueryTree
normalise t = N.toQueryTree (N.compile (ℐ.⟦ t ⟧tm (lift tt) .right .N.mor (tt , N.⟦extFunc⟧)))

correctness : (t : NetworkSpecification linear (linear , Ex)) →
              standard t ⇔ eval-QueryTree (normalise t)
correctness t =
  ⇔-trans
    (ExFormulaR-ok empty
      (compile-lemma linear empty _ q (ℐ.⟦ t ⟧tm (lift tt)
         .rel-mor empty (tt , extFunc) (tt , N.⟦extFunc⟧) (refl , h))))
    {!!} --(toPrenexForm-ok (N.compile q) empty-env)
  where q : N.LetLift N.ExFormula ε
        q = ℐ.⟦ t ⟧tm (lift tt) .right .N.mor (tt , N.⟦extFunc⟧)

        -- The real external function is related to the symbolic
        -- internal function under the VerifierLang semantics
        h : (⟦Num⟧ linear ⟦⇒⟧ LiftMR (⟦Num⟧ linear)) .rel _ extFunc N.⟦extFunc⟧
        h w' ρ x y refl = sym (*-identityˡ _)

