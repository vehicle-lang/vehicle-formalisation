{-# OPTIONS --postfix-projections #-}

open import Level using (0ℓ; suc; lift)

open import Data.Bool using (not; _∧_; _∨_; true; false)
                   renaming (Bool to 𝔹; T to True; if_then_else_ to ifᵇ_then_else_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Rational using (ℚ; _+_; _*_; _≤ᵇ_; _≟_; 1ℚ)
open import Data.Rational.Properties using (*-identityˡ; *-comm)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; sym; cong₂; subst; module ≡-Reasoning)

open import Util
open import MiniVehicle.Qualifiers
open import NormalisedExpr renaming (_∘_ to _∘r_)
open import Interpretation
open import EquiInhabited

module NormalisationCorrect (extFunc : ℚ → ℚ) where

  import StandardSemantics as S
  import Normalisation as N

  open Evaluation extFunc

  record World : Set where
    field
      ctxt : LinVarCtxt
      env  : Env ctxt
  open World public

  empty : World
  empty .ctxt = ε
  empty .env = empty-env

  -- World morphisms extend the context whilst making sure that the
  -- environment is preserved.
  record _⇒w_ (w₁ w₂ : World) : Set where
    field
      ren   : w₁ .ctxt ⇒ᵣ w₂ .ctxt
      presv : ∀ x → w₁ .env (ren x) ≡ w₂ .env x
  open _⇒w_ public

  id-w : ∀ {w} → w ⇒w w
  id-w .ren x = x
  id-w .presv x = refl

  _∘w_ : ∀ {w₁ w₂ w₃} → w₂ ⇒w w₃ → w₁ ⇒w w₂ → w₁ ⇒w w₃
  (f ∘w g) .ren x = g .ren (f .ren x)
  (f ∘w g) .presv x = trans (g .presv (f .ren x)) (f .presv x)

  extend-w : World → ℚ → World
  extend-w w q .ctxt = w .ctxt ,∙
  extend-w w q .env = extend-env (w .env) q

  under-w : ∀ {w₁ w₂ q} → (w₁ ⇒w w₂) → (extend-w w₁ q ⇒w extend-w w₂ q)
  under-w ρ .ren = under (ρ .ren)
  under-w ρ .presv zero = refl
  under-w ρ .presv (succ x) = ρ .presv x

  under-w' : ∀ {w₁ w₂ q₁ q₂} → (q₁ ≡ q₂) → (w₁ ⇒w w₂) → (extend-w w₁ q₁ ⇒w extend-w w₂ q₂)
  under-w' eq ρ .ren = under (ρ .ren)
  under-w' eq ρ .presv zero = eq
  under-w' eq ρ .presv (succ x) = ρ .presv x

  wk-w : ∀ {w q} → extend-w w q ⇒w w
  wk-w .ren = succ
  wk-w .presv x = refl

  ------------------------------------------------------------------------------
  -- Our category of related interpretations

  module 𝒩 = Model N.ℳ
  module 𝒮 = Model (S.ℳ extFunc)

  record WRel : Set (suc 0ℓ) where
    field
      Left  : 𝒮.⟦Type⟧
      Right : 𝒩.⟦Type⟧
      rel   : (w : World) → Left → Right .N.Carrier (w .ctxt) → Set
      ext   : ∀ {w w'} (ρ : w' ⇒w w) a b → rel w a b → rel w' a (Right .N.rename (ρ .ren) b)
  open WRel

  record _==>_ (X Y : WRel) : Set where
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
  Flat : Set → WRel
  Flat X .Left = X
  Flat X .Right = N.K X
  Flat X .rel w x₁ x₂ = x₁ ≡ x₂
  Flat X .ext ρ x₁ x₂ eq = eq

  elem : ∀ {A X} → A → X ==> Flat A
  elem a .left = 𝒮.elem a
  elem a .right = 𝒩.elem a
  elem a .rel-mor w _ _ _ = refl

  ------------------------------------------------------------------------------
  -- Products and terminal object
  ⟦⊤⟧ : WRel
  ⟦⊤⟧ .Left = ⊤
  ⟦⊤⟧ .Right = 𝒩.⟦⊤⟧
  ⟦⊤⟧ .rel w tt tt = ⊤
  ⟦⊤⟧ .ext ρ tt tt x = x

  ⟦terminal⟧ : ∀ {X} → X ==> ⟦⊤⟧
  ⟦terminal⟧ .left = 𝒮.⟦terminal⟧
  ⟦terminal⟧ .right = 𝒩.⟦terminal⟧
  ⟦terminal⟧ .rel-mor _ _ _ _ = tt

  _⟦×⟧_ : WRel → WRel → WRel
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

  _⟦⇒⟧_ : WRel → WRel → WRel
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

  ⟦∀⟧ : ∀ {I : Set} → (I → WRel) → WRel
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
  KR : Set → WRel
  KR X .Left = X
  KR X .Right = N.K X
  KR X .rel w x y = x ≡ y
  KR X .ext ρ x y eq = eq

  ⟦Index⟧ : ℕ → WRel
  ⟦Index⟧ n = KR (Fin n)

  ⟦idx⟧ : (n : ℕ)(i : Fin n) → ∀ {X} → X ==> ⟦Index⟧ n
  ⟦idx⟧ n i .left = 𝒮.⟦idx⟧ n i
  ⟦idx⟧ n i .right = 𝒩.⟦idx⟧ n i
  ⟦idx⟧ n i .rel-mor w _ _ _ = refl

  ------------------------------------------------------------------------------
  ext-evalLinExp :
    ∀ {w₁ w₂} e (ρ : w₂ ⇒w w₁) →
      eval-LinExp e (w₁ .env) ≡ eval-LinExp (rename-LinExp (ρ .ren) e) (w₂ .env)
  ext-evalLinExp (const q)   ρ = refl
  ext-evalLinExp (var q x)   ρ = cong (λ □ → q * □) (sym (ρ .presv x))
  ext-evalLinExp (e₁ `+` e₂) ρ = cong₂ _+_ (ext-evalLinExp e₁ ρ) (ext-evalLinExp e₂ ρ)

  ext-evalConstraint :
    ∀ {w₁ w₂} p (ρ : w₂ ⇒w w₁) →
      eval-Constraint p (w₁ .env)
      ≡ eval-Constraint (rename-Constraint (ρ .ren) p) (w₂ .env)
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
  ⟦Num⟧ : LinearityVal → WRel
  ⟦Num⟧ p .Left = 𝒮.⟦Num⟧ p
  ⟦Num⟧ p .Right = 𝒩.⟦Num⟧ p
  ⟦Num⟧ const .rel _ q₁ q₂ = q₁ ≡ q₂
  ⟦Num⟧ const .ext _ _ _ eq = eq
  ⟦Num⟧ linear .rel w x exp = x ≡ eval-LinExp exp (w .env)
  ⟦Num⟧ linear .ext ρ x exp eq = trans eq (ext-evalLinExp exp ρ)
  ⟦Num⟧ nonlinear .rel w x tt = ⊤
  ⟦Num⟧ nonlinear .ext _ _ _ _ = tt

  ⟦const⟧ : ∀ {X} → ℚ → X ==> ⟦Num⟧ const
  ⟦const⟧ q .left _ = q
  ⟦const⟧ q .right = 𝒩.⟦const⟧ q
  ⟦const⟧ q .rel-mor w _ _ _ = refl

  ⟦add⟧ : ∀ {l₁ l₂ l₃} →
           (Flat (MaxLinRel l₁ l₂ l₃) ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Num⟧ l₃
  ⟦add⟧ .left = 𝒮.⟦add⟧
  ⟦add⟧ .right = 𝒩.⟦add⟧
  ⟦add⟧ .rel-mor w (const-const   , x₁ , y₁) (_ , x₂ , y₂) (refl , x₁₂ , y₁₂) =
    cong₂ _+_ x₁₂ y₁₂
  ⟦add⟧ .rel-mor w (const-linear  , x₁ , y₁) (_ , x₂ , y₂) (refl , x₁₂ , y₁₂) =
    cong₂ _+_ x₁₂ y₁₂
  ⟦add⟧ .rel-mor w (linear-const  , x₁ , y₁) (_ , x₂ , y₂) (refl , x₁₂ , y₁₂) =
    cong₂ _+_ x₁₂ y₁₂
  ⟦add⟧ .rel-mor w (linear-linear , x₁ , y₁) (_ , x₂ , y₂) (refl , x₁₂ , y₁₂) =
    cong₂ _+_ x₁₂ y₁₂

  ⟦mul⟧ : ∀ {l₁ l₂ l₃} → (Flat (MulRel l₁ l₂ l₃) ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Num⟧ l₃
  ⟦mul⟧ .left = 𝒮.⟦mul⟧
  ⟦mul⟧ .right = 𝒩.⟦mul⟧
  ⟦mul⟧ .rel-mor w (const-const  , x₁ , y₁) (_ , x₂ , y₂) (refl , x₁₂ , y₁₂) =
    cong₂ _*_ x₁₂ y₁₂
  ⟦mul⟧ .rel-mor w (const-linear , x₁ , y₁) (_ , x₂ , y₂) (refl , x₁₂ , y₁₂) =
    trans (cong₂ _*_ x₁₂ y₁₂) (eval-⊛ x₂ y₂ (w .env))
  ⟦mul⟧ .rel-mor w (linear-const , x₁ , y₁) (_ , x₂ , y₂) (refl , x₁₂ , y₁₂) =
    trans (cong₂ _*_ x₁₂ y₁₂)
      (trans (*-comm (eval-LinExp x₂ (w .env)) y₂) (eval-⊛ y₂ x₂ (w .env)))

  ------------------------------------------------------------------------------
  -- Booleans and constraints

  data QueryR : ∀ w → S.Quant 𝔹 → Query (w .ctxt) → Set where
    q-constraint : ∀ {w b ϕ} →
                   eval-Constraint ϕ (w .env) ≡ b →
                   QueryR w (S.return b) (constraint ϕ)
    q-true       : ∀ {w x ϕ ψ₁ ψ₂} →
                   eval-Constraint ϕ (w .env) ≡ true →
                   QueryR w x ψ₁ →
                   QueryR w x ((constraint ϕ and ψ₁) or (constraint (negate ϕ) and ψ₂))
    q-false      : ∀ {w x ϕ ψ₁ ψ₂} →
                   eval-Constraint ϕ (w .env) ≡ false →
                   QueryR w x ψ₂ →
                   QueryR w x ((constraint ϕ and ψ₁) or (constraint (negate ϕ) and ψ₂))
    q-ex         : ∀ {w k ϕ} →
                   (∀ q → QueryR (extend-w w q) (k q) ϕ) →
                   QueryR w (S.ex k) (ex ϕ)
    q-ex'        : ∀ {w x ϕ ψ} q →
                   (∀ q' → (q' ≡ q) ⇔ True (eval-Constraint ϕ (extend-env (w .env) q'))) →
                   QueryR (extend-w w q) x ψ →
                   QueryR w x (ex (constraint ϕ and ψ))
    q-and        : ∀ {w ϕ₁ ϕ₂ ψ₁ ψ₂ } →
                   QueryR w ϕ₁ ψ₁ →
                   QueryR w ϕ₂ ψ₂ →
                   QueryR w (ϕ₁ S.and ϕ₂) (ψ₁ and ψ₂)
    q-or         : ∀ {w ϕ₁ ϕ₂ ψ₁ ψ₂ } →
                   QueryR w ϕ₁ ψ₁ →
                   QueryR w ϕ₂ ψ₂ →
                   QueryR w (ϕ₁ S.or ϕ₂) (ψ₁ or ψ₂)

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
    q-ex' q (λ q' → ⇔-trans (uniq q') (cong-True (ext-evalConstraint ϕ (under-w ρ))))
          (ext-Query (under-w ρ) _ _ r)
  ext-Query ρ _ _ (q-and r₁ r₂) = q-and (ext-Query ρ _ _ r₁) (ext-Query ρ _ _ r₂)
  ext-Query ρ _ _ (q-or r₁ r₂) = q-or (ext-Query ρ _ _ r₁) (ext-Query ρ _ _ r₂)

  ⟦Bool⟧ : LinearityVal → PolarityVal → WRel
  ⟦Bool⟧ l p .Left = 𝒮.⟦Bool⟧ l p
  ⟦Bool⟧ l p .Right = 𝒩.⟦Bool⟧ l p
  ⟦Bool⟧ l U .rel w b ϕ = b ≡ eval-Constraint ϕ (w .env)
  ⟦Bool⟧ l U .ext ρ b ϕ eq = trans eq (ext-evalConstraint ϕ ρ)
  ⟦Bool⟧ l Ex .rel = QueryR
  ⟦Bool⟧ l Ex .ext = ext-Query

  ⟦≤⟧ : ∀ {l₁ l₂ l₃} → (Flat (MaxLinRel l₁ l₂ l₃) ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Bool⟧ l₃ U
  ⟦≤⟧ .left = 𝒮.⟦≤⟧
  ⟦≤⟧ .right = 𝒩.⟦≤⟧
  ⟦≤⟧ .rel-mor w (const-const   , x₁ , y₁) (_ , x₂ , y₂) (refl , x₁₂ , y₁₂) =
    cong₂ _≤ᵇ_ x₁₂ y₁₂
  ⟦≤⟧ .rel-mor w (const-linear  , x₁ , y₁) (_ , x₂ , y₂) (refl , x₁₂ , y₁₂) =
    cong₂ _≤ᵇ_ x₁₂ y₁₂
  ⟦≤⟧ .rel-mor w (linear-const  , x₁ , y₁) (_ , x₂ , y₂) (refl , x₁₂ , y₁₂) =
    cong₂ _≤ᵇ_ x₁₂ y₁₂
  ⟦≤⟧ .rel-mor w (linear-linear , x₁ , y₁) (_ , x₂ , y₂) (refl , x₁₂ , y₁₂) =
    cong₂ _≤ᵇ_ x₁₂ y₁₂

  ⟦and⟧ : ∀ {l₁ l₂ l₃ p₁ p₂ p₃} →
            (Flat (MaxLinRel l₁ l₂ l₃) ⟦×⟧
             (Flat (MaxPolRel p₁ p₂ p₃) ⟦×⟧
              (⟦Bool⟧ l₁ p₁ ⟦×⟧ ⟦Bool⟧ l₂ p₂))) ==> ⟦Bool⟧ l₃ p₃
  ⟦and⟧ .left = 𝒮.⟦and⟧
  ⟦and⟧ .right = 𝒩.⟦and⟧
  ⟦and⟧ .rel-mor w (p , U-U , x₁ , y₁) (_ , _ , x₂ , y₂) (refl , refl , x₁₂ , y₁₂) =
    cong₂ _∧_ x₁₂ y₁₂
  ⟦and⟧ .rel-mor w (p , U-Ex , x₁ , y₁) (_ , _ , x₂ , y₂) (refl , refl , x₁₂ , y₁₂) =
    q-and (q-constraint (sym x₁₂)) y₁₂
  ⟦and⟧ .rel-mor w (p , Ex-U , x₁ , y₁) (_ , _ , x₂ , y₂) (refl , refl , x₁₂ , y₁₂) =
    q-and x₁₂ (q-constraint (sym y₁₂))
  ⟦and⟧ .rel-mor w (p , Ex-Ex , x₁ , y₁) (_ , _ , x₂ , y₂) (refl , refl , x₁₂ , y₁₂) =
    q-and x₁₂ y₁₂

  ⟦or⟧ : ∀ {l₁ l₂ l₃ p₁ p₂ p₃} →
            (Flat (MaxLinRel l₁ l₂ l₃) ⟦×⟧
             (Flat (MaxPolRel p₁ p₂ p₃) ⟦×⟧
              (⟦Bool⟧ l₁ p₁ ⟦×⟧ ⟦Bool⟧ l₂ p₂))) ==> ⟦Bool⟧ l₃ p₃
  ⟦or⟧ .left = 𝒮.⟦or⟧
  ⟦or⟧ .right = 𝒩.⟦or⟧
  ⟦or⟧ .rel-mor w (p , U-U , x₁ , y₁) (_ , _ , x₂ , y₂) (refl , refl , x₁₂ , y₁₂) =
    cong₂ _∨_ x₁₂ y₁₂
  ⟦or⟧ .rel-mor w (p , U-Ex , x₁ , y₁) (_ , _ , x₂ , y₂) (refl , refl , x₁₂ , y₁₂) =
    q-or (q-constraint (sym x₁₂)) y₁₂
  ⟦or⟧ .rel-mor w (p , Ex-U , x₁ , y₁) (_ , _ , x₂ , y₂) (refl , refl , x₁₂ , y₁₂) =
    q-or x₁₂ (q-constraint (sym y₁₂))
  ⟦or⟧ .rel-mor w (p , Ex-Ex , x₁ , y₁) (_ , _ , x₂ , y₂) (refl , refl , x₁₂ , y₁₂) =
    q-or x₁₂ y₁₂

  ⟦not⟧ : ∀ {l p₁ p₂} → (Flat (NegPolRel p₁ p₂) ⟦×⟧ ⟦Bool⟧ l p₁) ==> ⟦Bool⟧ l p₂
  ⟦not⟧ .left = 𝒮.⟦not⟧
  ⟦not⟧ {l} .right = 𝒩.⟦not⟧ {l = l}
  ⟦not⟧ .rel-mor w (U , x₁) (_ , x₂) (refl , x₁₂) =
    trans (cong not x₁₂) (eval-negate x₂ (w .env))

  ------------------------------------------------------------------------------
  module _ (X : WRel) where

    LetLiftR : (w : World) → X .Left → N.LetLift (X .Right .N.Carrier) (w .ctxt) → Set
    LetLiftR w a (N.return b) = X .rel w a b
    LetLiftR w a (N.if c k₁ k₂) =
      ifᵇ (eval-Constraint c (w .env))
       then LetLiftR w a k₁
       else LetLiftR w a k₂
    LetLiftR w a (N.let-linexp e k) =
      LetLiftR (extend-w w (eval-LinExp e (w .env))) a k
    LetLiftR w a (N.let-funexp x k) =
      LetLiftR (extend-w w (extFunc (w .env x))) a k

    ext-lift : ∀ {w₁ w₂} (ρ : w₂ ⇒w w₁) la lb →
               LetLiftR w₁ la lb →
               LetLiftR w₂ la (N.rename-lift (X .Right .N.rename) (ρ .ren) lb)
    ext-lift ρ a (N.return b) = X .ext ρ a b
    ext-lift {w₁} ρ a (N.if c tru fal) rewrite sym (ext-evalConstraint c ρ) with eval-Constraint c (w₁ .env)
    ... | false = ext-lift ρ a fal
    ... | true  = ext-lift ρ a tru
    ext-lift ρ a (N.let-linexp x lb) =
      ext-lift (under-w' (sym (ext-evalLinExp x ρ)) ρ) a lb
    ext-lift ρ a (N.let-funexp x lb) =
      ext-lift (under-w' (cong extFunc (ρ .presv x)) ρ) a lb

    LiftMR : WRel
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
  let-bindR w x₁ (N.if c x₂₁ x₂₂) f g r-x₁x₂ r-fg with eval-Constraint c (w .env)
  ... | true = let-bindR w x₁ x₂₁ f g r-x₁x₂ r-fg
  ... | false = let-bindR w x₁ x₂₂ f g r-x₁x₂ r-fg
  let-bindR w x₁ (N.let-linexp e x₂) f g r-x₁x₂ r-fg =
    let-bindR (extend-w w (eval-LinExp e (w .env)))
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

  ⟦extFunc⟧ : ⟦Num⟧ linear ==> LiftMR (⟦Num⟧ linear)
  ⟦extFunc⟧ .left = 𝒮.⟦extFunc⟧
  ⟦extFunc⟧ .right = 𝒩.⟦extFunc⟧
  ⟦extFunc⟧ .rel-mor w x₁ x₂ r-x₁x₂ =
    trans (cong extFunc r-x₁x₂) (sym (*-identityˡ _))

  ⟦if⟧ : ∀ {X} → ((LiftMR X ⟦×⟧ LiftMR X) ⟦×⟧ ⟦Bool⟧ linear U) ==> LiftMR X
  ⟦if⟧ .left = 𝒮.⟦if⟧
  ⟦if⟧ .right = 𝒩.⟦if⟧
  ⟦if⟧ .rel-mor w ((tr₁ , fa₁) , false) ((tr₂ , fa₂) , ϕ) ((tr₁-tr₂ , fa₁-fa₂) , eq) rewrite sym eq = fa₁-fa₂
  ⟦if⟧ .rel-mor w ((tr₁ , fa₁) , true) ((tr₂ , fa₂) , ϕ) ((tr₁-tr₂ , fa₁-fa₂) , eq) rewrite sym eq = tr₁-tr₂

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

  compile-lemma : ∀ l w x₁ x₂ → LetLiftR (⟦Bool⟧ l Ex) w x₁ x₂ → QueryR w x₁ (N.compile x₂)
  compile-lemma l w x₁ (N.return x) r = r
  compile-lemma l w x₁ (N.if ϕ tr fa) r with is-true-or-false (eval-Constraint ϕ (w .env))
  ... | inj₁ is-true =
         q-true is-true (compile-lemma l w _ tr (subst (λ □ → ifᵇ □ then _ else _) is-true r))
  ... | inj₂ is-false =
         q-false is-false (compile-lemma l w _ fa (subst (λ □ → ifᵇ □ then _ else _) is-false r))
  compile-lemma l w x₁ (N.let-linexp e k) r =
    q-ex' q
          (λ q' →
            ⇔-trans (eq-cong
                      (sym (*-identityˡ q'))
                      (ext-evalLinExp e wk-w))
             (⇔-sym (does-cong (1ℚ * q' ≟
                                eval-LinExp (rename-LinExp succ e) (extend-env (w .env) q')))))
          (compile-lemma l (extend-w w q) x₁ k r)
    where q : ℚ
          q = eval-LinExp e (w .env)
  compile-lemma l w x₁ (N.let-funexp x k) r =
    q-ex' q
          (λ q' → ⇔-sym (does-cong (q' ≟ extFunc (w .env x))))
          (compile-lemma l (extend-w w q) x₁ k r)
    where q : ℚ
          q = extFunc (w .env x)

  ⟦∃⟧ : ∀ {p₁ p₂ l} →
       (Flat (QuantifyRel p₁ p₂) ⟦×⟧ (⟦Num⟧ linear ⟦⇒⟧ LiftMR (⟦Bool⟧ l p₁))) ==> ⟦Bool⟧ l p₂
  ⟦∃⟧ .left = 𝒮.⟦∃⟧
  ⟦∃⟧ {l = l} .right = 𝒩.⟦∃⟧ {l = l}
  ⟦∃⟧ {l = l} .rel-mor w (U  , f₁) (_ , f₂) (refl , r) =
    q-ex (λ q → compile-lemma l (extend-w w q)
                     (S.return (f₁ q))
                     (N.bind-let (f₂ (w .ctxt ,∙) succ (var 1ℚ zero))
                       (λ Δ' ρ ϕ → N.return (constraint ϕ)))
                     (let-bindR (extend-w w q)
                       (f₁ q)
                       (f₂ (w .ctxt ,∙) succ (var 1ℚ zero))
                       S.return
                       _
                       (r (extend-w w q) wk-w q (var 1ℚ zero) (sym (*-identityˡ q)))
                       λ w' ρ a b x → q-constraint (sym x)))
  ⟦∃⟧ {l = l} .rel-mor w (Ex , f₁) (_ , f₂) (refl , r) =
    q-ex λ q → compile-lemma l (extend-w w q) (f₁ q) (f₂ (w .ctxt ,∙) succ (var 1ℚ zero))
                 (r (extend-w w q) wk-w q (var 1ℚ zero) (sym (*-identityˡ q)))

  QueryR-ok : ∀ w {x₁ x₂} →
                QueryR w x₁ x₂ →
                S.eval-Quant x₁ True ⇔ eval-Query x₂ (w .env)
  QueryR-ok w (q-constraint x) = cong-True (sym x)
  QueryR-ok w (q-true {ϕ = ϕ} is-true r) =
    ⇔-trans (QueryR-ok w r)
    (⇔-trans or-left
            (⊎-cong (⇔-trans ⊤-fst (×-cong (⊤-bool is-true) ⇔-refl))
                    (⇔-trans ⊥-fst (×-cong (⊥-bool (trans (sym (eval-negate ϕ (w .env))) (cong not is-true)))
                                           ⇔-refl))))
  QueryR-ok w (q-false {ϕ = ϕ} is-false r) =
    ⇔-trans (QueryR-ok w r)
    (⇔-trans or-right
    (⊎-cong
      (⇔-trans ⊥-fst (×-cong
                       (⊥-bool is-false)
                       ⇔-refl))
      (⇔-trans ⊤-fst (×-cong
                       (⊤-bool (trans (sym (eval-negate ϕ (w .env))) (cong not is-false)))
                       ⇔-refl))))
  QueryR-ok w (q-ex x) = cong-∃ (λ q → QueryR-ok (extend-w w q) (x q))
  QueryR-ok w (q-ex' q x r) =
    ⇔-trans (QueryR-ok (extend-w w q) r)
             (⇔-trans (known q) (cong-∃ (λ q' → ×-cong (x q') ⇔-refl)))
  QueryR-ok w (q-and r₁ r₂) = ×-cong (QueryR-ok w r₁) (QueryR-ok w r₂)
  QueryR-ok w (q-or r₁ r₂) = ⊎-cong (QueryR-ok w r₁) (QueryR-ok w r₂)


  ext-FlatQuery : ∀ {w₁ w₂} (ρ : w₂ ⇒w w₁) ϕ →
                  eval-FlatQuery ϕ (w₁ .env) ⇔
                     eval-FlatQuery (rename-FlatQuery (ρ .ren) ϕ) (w₂ .env)
  ext-FlatQuery ρ (constraint ϕ) = cong-True (ext-evalConstraint ϕ ρ)
  ext-FlatQuery ρ (ex ϕ) = cong-∃ λ q → ext-FlatQuery (under-w ρ) ϕ

  equi-conj-constraint : ∀ {Δ} (ϕ : Constraint Δ) ψ η →
                         (True (eval-Constraint ϕ η) × eval-FlatQuery ψ η)
                            ⇔ eval-FlatQuery (conj-constraint ϕ ψ) η
  equi-conj-constraint ϕ (constraint x) η = True-∧
  equi-conj-constraint ϕ (ex ψ) η =
    ⇔-trans
      and-comm-left
      (⇔-trans
       (cong-∃ λ q → ×-cong (cong-True (ext-evalConstraint ϕ wk-w)) ⇔-refl)
       (cong-∃ λ q →
          equi-conj-constraint (rename-Constraint succ ϕ) ψ (extend-env η q)))

  equi-conj : ∀ {Δ} (ϕ : FlatQuery Δ) ψ η →
              (eval-FlatQuery ϕ η × eval-FlatQuery ψ η) ⇔ eval-FlatQuery (conj ϕ ψ) η
  equi-conj (constraint ϕ) ψ η = equi-conj-constraint ϕ ψ η
  equi-conj (ex ϕ) ψ η =
    ⇔-trans
     and-comm-right
     (cong-∃ λ q →
      ⇔-trans
       (×-cong ⇔-refl (ext-FlatQuery wk-w ψ))
       (equi-conj ϕ (rename-FlatQuery succ ψ) (extend-env η q)))

  equi-disj-constraint : ∀ {Δ} (ϕ : Constraint Δ) ψ η →
                         (True (eval-Constraint ϕ η) ⊎ eval-FlatQuery ψ η)
                            ⇔ eval-FlatQuery (disj-constraint ϕ ψ) η
  equi-disj-constraint ϕ (constraint x) η = True-∨
  equi-disj-constraint ϕ (ex ψ) η =
    ⇔-trans
     (or-comm-right 1ℚ)
     (cong-∃
      λ q → ⇔-trans
             (⊎-cong (cong-True (ext-evalConstraint ϕ wk-w)) ⇔-refl)
             (equi-disj-constraint (rename-Constraint succ ϕ) ψ (extend-env η q)))

  equi-disj : ∀ {Δ} (ϕ : FlatQuery Δ) ψ η →
              (eval-FlatQuery ϕ η ⊎ eval-FlatQuery ψ η) ⇔ eval-FlatQuery (disj ϕ ψ) η
  equi-disj (constraint ϕ) ψ η = equi-disj-constraint ϕ ψ η
  equi-disj (ex ϕ) ψ η =
    ⇔-trans (or-comm-left 1ℚ)
     (cong-∃ λ q →
      ⇔-trans
       (⊎-cong ⇔-refl (ext-FlatQuery wk-w ψ))
       (equi-disj ϕ (rename-FlatQuery succ ψ) (extend-env η q)))

  flatten-ok : ∀ {Δ} (ϕ : Query Δ) η →
               eval-Query ϕ η ⇔ eval-FlatQuery (flatten ϕ) η
  flatten-ok (constraint x) η = ⇔-refl
  flatten-ok (ex ϕ) η = cong-∃ λ q → flatten-ok ϕ (extend-env η q)
  flatten-ok (ϕ and ψ) η =
    ⇔-trans (×-cong (flatten-ok ϕ η) (flatten-ok ψ η))
              (equi-conj (flatten ϕ) (flatten ψ) η)
  flatten-ok (ϕ or ψ) η =
    ⇔-trans (⊎-cong (flatten-ok ϕ η) (flatten-ok ψ η))
              (equi-disj (flatten ϕ) (flatten ψ) η)

  ℳ : Model (suc 0ℓ) 0ℓ
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
  ℳ .Model.Mon = LiftMR
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
  ℳ .Model.⟦if⟧ = ⟦if⟧
  ℳ .Model.⟦Index⟧ = ⟦Index⟧
  ℳ .Model.⟦idx⟧ = ⟦idx⟧
  ℳ .Model.⟦∃⟧ = ⟦∃⟧

  open import MiniVehicle hiding (_⇒ᵣ_; under)

  module ℐ = Interpret ℳ

  standard : ε / ε ⊢ Bool (LinearityConst linear) (PolarityConst Ex) → Set
  standard t = S.eval-Quant (ℐ.⟦ t ⟧tm (lift tt) .left tt) True

  normalise : ε / ε ⊢ Bool (LinearityConst linear) (PolarityConst Ex) → FlatQuery ε
  normalise t = flatten (N.compile (ℐ.⟦ t ⟧tm (lift tt) .right .N.mor tt))

  full-correctness : (t : ε / ε ⊢ Bool (LinearityConst linear) (PolarityConst Ex)) →
                     standard t ⇔ eval-FlatQuery (normalise t) (empty .env)
  full-correctness t =
    ⇔-trans
      (QueryR-ok empty (compile-lemma linear empty _ q (ℐ.⟦ t ⟧tm (lift tt) .rel-mor empty tt tt tt)))
      (flatten-ok (N.compile q) empty-env)
    where q : N.LetLift Query ε
          q = ℐ.⟦ t ⟧tm (lift tt) .right .N.mor tt
