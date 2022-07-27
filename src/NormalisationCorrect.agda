{-# OPTIONS --postfix-projections --safe #-}

module NormalisationCorrect where

open import Data.Bool using (not; _∧_; _∨_; true; false)
                   renaming (Bool to 𝔹; if_then_else_ to ifᵇ_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Rational using (ℚ; _+_; _*_; _≤ᵇ_; _≟_)
open import Data.Rational.Properties using (*-identityˡ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (does)

open import MiniVehicle
open import NormalisedExpr
import StandardSemantics as S
import Normalisation as N

------------------------------------------------------------------------------
-- worlds are pairs of LinVarCtxts and Environments for them

record World : Set where
  constructor _,_
  field
    ctxt : LinVarCtxt
    env  : Env ctxt
open World

-- world morphisms extend the context so that the environment is
-- preserved
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

------------------------------------------------------------------------------

WRel : Set → (LinVarCtxt → Set) → Set₁
WRel A B = ∀ (w : World) → A → B (w .ctxt) → Set

-- FIXME: move to NormalisationExpr
extend-env : ∀ {Δ} → Env Δ → ℚ → Env (Δ ,∙)
extend-env η q zero     = q
extend-env η q (succ x) = η x

module _ (extFunc : ℚ → ℚ) where

  LetLiftR : ∀ {A B} → WRel A B → WRel A (LetLift B)
  LetLiftR R w a (return b) = R w a b
  LetLiftR R w a (if c k₁ k₂) =
    ifᵇ (eval-ConstraintExp extFunc c (w .env))
     then LetLiftR R w a k₁
     else LetLiftR R w a (k₂ (λ x → x))
  LetLiftR R w a (let-linexp e k) =
    LetLiftR R ((w .ctxt ,∙) , extend-env (w .env) (eval-LinExp e (w .env))) a k
  LetLiftR R w a (let-funexp x k) =
    LetLiftR R (((w .ctxt ,∙) , extend-env (w .env) (extFunc (w .env x)))) a k

  let-bindR : ∀ {A A' B B'}{RA : WRel A A'}{RB : WRel B B'} w x y (f : A → B) g →
    LetLiftR RA w x y →
    (∀ w' (ρ : w' ⇒w w) a b → RA w' a b → LetLiftR RB w' (f a) (g (w' .ctxt) (ρ .ren) b)) →
    LetLiftR RB w (f x) (bind-let y g)
  let-bindR w x (return y) f g r-xy r-fg = r-fg w id-w x y r-xy
  let-bindR w x (if e y₁ y₂) f g r-xy r-fg with eval-ConstraintExp extFunc e (w .env)
  ... | true  = let-bindR w x y₁ f g r-xy r-fg
  ... | false = let-bindR w x (y₂ (λ x → x)) f g r-xy r-fg
  let-bindR w x (let-linexp e y) f g r-xy r-fg =
    let-bindR
      ((w .ctxt ,∙) , extend-env (w .env) (eval-LinExp e (w .env)))
      x
      y
      f
      (λ Δ' ρ a' → g Δ' (λ x₁ → ρ (succ x₁)) a')
      r-xy
      λ w' ρ a b r-ab →
        r-fg
          w' (record { ren = λ x₁ → ρ .ren (succ x₁) ; presv = λ x₁ → ρ .presv (succ x₁) })
          a b r-ab
          -- FIXME: tidy up this 'record' bit
  let-bindR w x (let-funexp v y) f g r-xy r-fg =
    let-bindR
      ((w .ctxt ,∙) , extend-env (w .env) (extFunc (w .env v)))
      x
      y
      f
      (λ Δ' ρ a' → g Δ' (λ x₁ → ρ (succ x₁)) a')
      r-xy
      λ w' ρ a b r-ab →
        r-fg w' (record { ren = λ x₁ → ρ .ren (succ x₁) ; presv = λ x₁ → ρ .presv (succ x₁) })
        a b r-ab


  ------------------------------------------------------------------------------
  ext-evalLinExp :
    ∀ {w₁ w₂} e (ρ : w₂ ⇒w w₁) →
      eval-LinExp e (w₁ .env) ≡ eval-LinExp (rename-LinExp (ρ .ren) e) (w₂ .env)
  ext-evalLinExp (const q)  ρ = refl
  ext-evalLinExp (var q x)  ρ = cong (λ □ → q * □) (sym (ρ .presv x))
  ext-evalLinExp (e₁ `+ e₂) ρ = cong₂ _+_ (ext-evalLinExp e₁ ρ) (ext-evalLinExp e₂ ρ)

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
  -- Relatedness for types
  ⟦_⟧ty : ∀ A → WRel S.⟦ A ⟧ty N.⟦ A ⟧ty
  ⟦ Bool constraint ⟧ty w x y = x ≡ eval-ConstraintExp extFunc y (w .env)
  ⟦ Num const ⟧ty       w x y = x ≡ y
  ⟦ Num linear ⟧ty      w x y = x ≡ eval-LinExp y (w .env)
  ⟦ A ⇒ B ⟧ty          w f g =
    ∀ w' (ρ : w' ⇒w w) x y →
      ⟦ A ⟧ty w' x y →
      LetLiftR ⟦ B ⟧ty w' (f x) (g (w' .ctxt) (ρ .ren) y)

  ext-ty : ∀ A {w₁ w₂} → (ρ : w₂ ⇒w w₁) → ∀ {x y} →
           ⟦ A ⟧ty w₁ x y →
           ⟦ A ⟧ty w₂ x (N.rename-ty A (ρ .ren) y)
  ext-ty (Bool constraint) ρ {x}{y} r =
    trans r (ext-evalConstraint y ρ)
  ext-ty (Num const) ρ r = r
  ext-ty (Num linear) ρ {x}{y} r = trans r (ext-evalLinExp y ρ)
  ext-ty (A ⇒ B) ρ r =
    λ w₃ ρ₁ x₁ y₁ r₂ → r w₃ (ρ ∘w ρ₁) x₁ y₁ r₂

  -- Relatedness for contexts
  ⟦_⟧ctxt : ∀ Γ → WRel S.⟦ Γ ⟧ctxt N.⟦ Γ ⟧ctxt
  ⟦ ε ⟧ctxt      w tt      tt       = ⊤
  ⟦ Γ ,- A ⟧ctxt w (γₛ , x) (γₙ , y) = ⟦ Γ ⟧ctxt w γₛ γₙ × ⟦ A ⟧ty w x y

  ext-ctxt : ∀ Γ {w₁ w₂} (ρ : w₂ ⇒w w₁) → ∀ {x y} →
             ⟦ Γ ⟧ctxt w₁ x y →
             ⟦ Γ ⟧ctxt w₂ x (N.rename-ctxt (ρ .ren) y)
  ext-ctxt ε ρ r = tt
  ext-ctxt (Γ ,- A) ρ (γ₁γ₂ , a₁a₂) =
    (ext-ctxt Γ ρ γ₁γ₂) , (ext-ty A ρ a₁a₂)

  -- Variables' interpretations are related
  ⟦_⟧var : ∀ {Γ A} (x : Γ ∋ A) w {γₛ γₙ} →
          ⟦ Γ ⟧ctxt w γₛ γₙ →
          ⟦ A ⟧ty w (S.⟦ x ⟧var γₛ) (N.⟦ x ⟧var γₙ)
  ⟦ zero ⟧var   w (_    , x-y) = x-y
  ⟦ succ x ⟧var w (γₛ-γₙ , _  ) = ⟦ x ⟧var w γₛ-γₙ

  module ST = S.TermSem (extFunc)

  -- Terms' interpretations are related
  ⟦_⟧tm : ∀ {Γ A} (x : Γ ⊢ A) w {γₛ γₙ} →
          ⟦ Γ ⟧ctxt w γₛ γₙ →
          LetLiftR ⟦ A ⟧ty w (ST.⟦ x ⟧tm γₛ) (N.⟦ x ⟧tm γₙ)
  ⟦ var x ⟧tm w γ₁-γ₂ = ⟦ x ⟧var w γ₁-γ₂
  ⟦ ƛ t ⟧tm w γ₁-γ₂ =
    λ w' ρ x y x-y → ⟦ t ⟧tm w' (ext-ctxt _ ρ γ₁-γ₂ , x-y)
  ⟦ s ∙ t ⟧tm w {γₛ}{γₙ} γ₁-γ₂ =
    let-bindR w (ST.⟦ s ⟧tm γₛ) (N.⟦ s ⟧tm γₙ)
      _ -- (λ a → a (S.⟦ t ⟧tm γₛ))
      _
      (⟦ s ⟧tm w γ₁-γ₂)
      λ w' ρ a b r-ab →
        let-bindR w' (ST.⟦ t ⟧tm γₛ) (N.⟦ t ⟧tm (N.rename-ctxt (ρ .ren) γₙ))
          _ -- (λ a' → a a')
          _
          (⟦ t ⟧tm w' (ext-ctxt _ ρ γ₁-γ₂))
          r-ab
  ⟦ func t ⟧tm w {γₛ}{γₙ} γ₁-γ₂ =
    let-bindR w (ST.⟦ t ⟧tm γₛ) (N.⟦ t ⟧tm γₙ)
      extFunc
      _
      (⟦ t ⟧tm w γ₁-γ₂)
      λ { w' ρ a b refl → sym (*-identityˡ _) }
  ⟦ const x ⟧tm w γ₁-γ₂ = refl
  ⟦ lift t ⟧tm w {γₛ}{γₙ} γ₁-γ₂ =
    let-bindR w (ST.⟦ t ⟧tm γₛ) (N.⟦ t ⟧tm γₙ)
     (λ a → a)
     (λ _ _ q → return (const q))
     (⟦ t ⟧tm w γ₁-γ₂)
     λ w' ρ a b a≡b → a≡b
  ⟦ s `+ t ⟧tm w {γₛ}{γₙ} γ₁-γ₂ =
    let-bindR w (ST.⟦ s ⟧tm γₛ) (N.⟦ s ⟧tm γₙ)
      (λ a → a + ST.⟦ t ⟧tm γₛ)
      _
      (⟦ s ⟧tm w γ₁-γ₂)
      λ w' ρ a b r-ab →
        let-bindR w' (ST.⟦ t ⟧tm γₛ) (N.⟦ t ⟧tm (N.rename-ctxt (ρ .ren) γₙ))
          (λ b → a + b)
          _
          (⟦ t ⟧tm w' (ext-ctxt _ ρ γ₁-γ₂))
          λ w'' ρ₁ a₁ b₁ r-a₁b₁ →
            cong₂ _+_ (trans r-ab (ext-evalLinExp b ρ₁)) r-a₁b₁
  ⟦ s `* t ⟧tm w {γₛ}{γₙ} γ₁-γ₂ =
    let-bindR w (ST.⟦ s ⟧tm γₛ) (N.⟦ s ⟧tm γₙ)
      (λ a → a * ST.⟦ t ⟧tm γₛ)
      _
      (⟦ s ⟧tm w γ₁-γ₂)
      λ w' ρ a b r-ab →
        let-bindR w' (ST.⟦ t ⟧tm γₛ) (N.⟦ t ⟧tm (N.rename-ctxt (ρ .ren) γₙ))
          (λ b → a * b)
          _
          (⟦ t ⟧tm w' (ext-ctxt _ ρ γ₁-γ₂))
          λ w'' ρ₁ a₁ b₁ r-a₁b₁ →
            trans (cong₂ _*_ r-ab r-a₁b₁)
                  (eval-⊛ b b₁ (w'' .env))
  ⟦ s `≤ t ⟧tm w {γₛ}{γₙ} γ₁-γ₂ =
    let-bindR w (ST.⟦ s ⟧tm γₛ) (N.⟦ s ⟧tm γₙ)
      (λ a → a ≤ᵇ ST.⟦ t ⟧tm γₛ)
      _
      (⟦ s ⟧tm w γ₁-γ₂)
      λ w' ρ a b r-ab →
        let-bindR w' (ST.⟦ t ⟧tm γₛ) (N.⟦ t ⟧tm (N.rename-ctxt (ρ .ren) γₙ))
          (λ b → a ≤ᵇ b)
          _
          (⟦ t ⟧tm w' (ext-ctxt _ ρ γ₁-γ₂))
          λ w'' ρ₁ a₁ b₁ r-a₁b₁ →
            cong₂ _≤ᵇ_ (trans r-ab (ext-evalLinExp b ρ₁)) r-a₁b₁
  ⟦ if s then t else u ⟧tm w {γₛ}{γₙ} γ₁-γ₂ =
    let-bindR w (ST.⟦ s ⟧tm γₛ) (N.⟦ s ⟧tm γₙ)
      (λ a → ifᵇ a then ST.⟦ t ⟧tm γₛ else ST.⟦ u ⟧tm γₛ)
      _
      (⟦ s ⟧tm w γ₁-γ₂)
      r
    where r : ∀ w' (ρ : w' ⇒w w) a b →
              ⟦ Bool constraint ⟧ty w' a b →
              LetLiftR ⟦ _ ⟧ty w'
                (ifᵇ a then ST.⟦ t ⟧tm γₛ else ST.⟦ u ⟧tm γₛ)
                (if b (N.⟦ t ⟧tm (N.rename-ctxt (ρ .ren) γₙ))
                      (λ ρ' → N.⟦ u ⟧tm (N.rename-ctxt (ρ .ren ∘ ρ') γₙ)))
          r w' ρ false b eq rewrite sym eq = ⟦ u ⟧tm w' (ext-ctxt _ ρ γ₁-γ₂)
          r w' ρ true b eq rewrite sym eq = ⟦ t ⟧tm w' (ext-ctxt _ ρ γ₁-γ₂)
  ⟦ `¬ t ⟧tm w {γₛ}{γₙ} γ₁-γ₂ =
    let-bindR w (ST.⟦ t ⟧tm γₛ) (N.⟦ t ⟧tm γₙ)
      not
      (λ _ _ x → return (negate x))
      (⟦ t ⟧tm w γ₁-γ₂)
      λ { w' ρ a b refl → eval-negate extFunc b (w' .env) }
  ⟦ s `∧ t ⟧tm w {γₛ}{γₙ} γ₁-γ₂ =
    let-bindR w (ST.⟦ s ⟧tm γₛ) (N.⟦ s ⟧tm γₙ)
      (λ a → a ∧ ST.⟦ t ⟧tm γₛ)
      _
      (⟦ s ⟧tm w γ₁-γ₂)
      λ w' ρ a b r-ab →
        let-bindR w' (ST.⟦ t ⟧tm γₛ) (N.⟦ t ⟧tm (N.rename-ctxt (ρ .ren) γₙ))
          (λ b → a ∧ b)
          _
          (⟦ t ⟧tm w' (ext-ctxt _ ρ γ₁-γ₂))
          λ w'' ρ₁ a₁ b₁ r-a₁b₁ →
          cong₂ _∧_ (trans r-ab (ext-evalConstraint b ρ₁)) r-a₁b₁
  ⟦ s `∨ t ⟧tm w {γₛ}{γₙ} γ₁-γ₂ =
    let-bindR w (ST.⟦ s ⟧tm γₛ) (N.⟦ s ⟧tm γₙ)
      (λ a → a ∨ ST.⟦ t ⟧tm γₛ)
      _
      (⟦ s ⟧tm w γ₁-γ₂)
      λ w' ρ a b r-ab →
        let-bindR w' (ST.⟦ t ⟧tm γₛ) (N.⟦ t ⟧tm (N.rename-ctxt (ρ .ren) γₙ))
          (λ b → a ∨ b)
          _
          (⟦ t ⟧tm w' (ext-ctxt _ ρ γ₁-γ₂))
          λ w'' ρ₁ a₁ b₁ r-a₁b₁ →
          cong₂ _∨_ (trans r-ab (ext-evalConstraint b ρ₁)) r-a₁b₁


    -- FIXME: lemmas for unary and binary operators?
    -- FIXME: would be easier to uncurry and have a lift2 operation:
    ---   lift2 : (A × B ⇒ₖ C) → LetLift A → LetLift B → LetLift C
