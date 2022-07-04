{-# OPTIONS --postfix-projections #-}
module NormalisationCorrect where

open import MiniVehicle
open import norm-expr
import StandardSemantics as S
import Normalisation as N
open import Data.Bool renaming (if_then_else_ to ifᵇ_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Rational using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- worlds are now pairs of LinVarCtxts and Environments for them

record World : Set where
  constructor _,_
  field
    ctxt : LinVarCtxt
    env  : Env ctxt
open World

record _⇒w_ (w₁ w₂ : World) : Set where
  field
    ren   : w₁ .ctxt ⇒ᵣ w₂ .ctxt
    presv : ∀ x → w₁ .env (ren x) ≡ w₂ .env x
open _⇒w_

WRel : Set → (LinVarCtxt → Set) → Set₁
WRel A B = ∀ (w : World) → A → B (w .ctxt) → Set

-- FIXME: move to norm-expr
extend-env : ∀ {Δ} → Env Δ → ℚ → Env (Δ ,∙)
extend-env η q zero     = q
extend-env η q (succ x) = η x

LetLiftR : ∀ {A B} → WRel A B → WRel A (LetLift B)
LetLiftR R w a (return b) = R w a b
LetLiftR R w a (if c k₁ k₂) =
  ifᵇ (eval-ConstraintExp c (w .env))
   then LetLiftR R w a k₁
   else LetLiftR R w a (k₂ (λ x → x))
LetLiftR R w a (let-exp e k) =
  LetLiftR R ((w .ctxt ,∙) , extend-env (w .env) (eval-LinExp e (w .env))) a k

-- FIXME: lemma on how LetLiftR interacts with let-bind

-- Relatedness for types
⟦_⟧ty : ∀ A → WRel S.⟦ A ⟧ty N.⟦ A ⟧ty
⟦ Bool constraint ⟧ty w x y = x ≡ eval-ConstraintExp y (w .env)
⟦ Num const ⟧ty       w x y = x ≡ y
⟦ Num linear ⟧ty      w x y = x ≡ eval-LinExp y (w .env)
⟦ A ⇒ B ⟧ty          w f g =
  ∀ w' (ρ : w' ⇒w w) x y →
    ⟦ A ⟧ty w' x y →
    LetLiftR ⟦ B ⟧ty w' (f x) (g (w' .ctxt) (ρ .ren) y)

-- FIXME: ⟦_⟧ty is preserved by _⇒w_

-- Relatedness for contexts
⟦_⟧ctxt : ∀ Γ → WRel S.⟦ Γ ⟧ctxt N.⟦ Γ ⟧ctxt
⟦ ε ⟧ctxt      w tt      tt       = ⊤
⟦ Γ ,- A ⟧ctxt w (γₛ , x) (γₙ , y) = ⟦ Γ ⟧ctxt w γₛ γₙ × ⟦ A ⟧ty w x y

-- FIXME: ⟦_⟧ctxt is preserved by _⇒w_

⟦_⟧var : ∀ {Γ A} (x : Γ ∋ A) w {γₛ γₙ} →
        ⟦ Γ ⟧ctxt w γₛ γₙ →
        ⟦ A ⟧ty w (S.⟦ x ⟧var γₛ) (N.⟦ x ⟧var γₙ)
⟦ zero ⟧var   w (_    , x-y) = x-y
⟦ succ x ⟧var w (γₛ-γₙ , _  ) = ⟦ x ⟧var w γₛ-γₙ

⟦_⟧tm : ∀ {Γ A} (x : Γ ⊢ A) w {γₛ γₙ} →
        ⟦ Γ ⟧ctxt w γₛ γₙ →
        LetLiftR ⟦ A ⟧ty w (S.⟦ x ⟧tm γₛ) (N.⟦ x ⟧tm γₙ)
⟦ var x ⟧tm w γ₁-γ₂ = ⟦ x ⟧var w γ₁-γ₂
⟦ ƛ t ⟧tm w γ₁-γ₂ =
  λ w' ρ x y x-y → ⟦ t ⟧tm w' ({!!} , x-y)
⟦ s ∙ t ⟧tm w γ₁-γ₂ = {!!}
⟦ const x ⟧tm w γ₁-γ₂ = refl
⟦ lift t ⟧tm w γ₁-γ₂ = {!!}
⟦ s `+ t ⟧tm w γ₁-γ₂ = {!!}
⟦ s `* t ⟧tm w γ₁-γ₂ = {!!}
⟦ s `≤ t ⟧tm w γ₁-γ₂ = {!!}
⟦ if s then t else u ⟧tm w γ₁-γ₂ = {!!}
⟦ `¬ t ⟧tm w γ₁-γ₂ = {!!}
⟦ t `∧ t₁ ⟧tm w γ₁-γ₂ = {!!}
⟦ t `∨ t₁ ⟧tm w γ₁-γ₂ = {!!}
