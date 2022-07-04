{-# OPTIONS --postfix-projections #-}
module NormalisationCorrect where

open import MiniVehicle
open import norm-expr
import StandardSemantics as S
import Normalisation as N
open import Data.Bool renaming (Bool to 𝔹; if_then_else_ to ifᵇ_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Rational using (ℚ; _+_; _*_; _≤ᵇ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

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

id-w : ∀ {w} → w ⇒w w
id-w .ren x = x
id-w .presv x = refl

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

-- Does this need to be upgraded to be strong?
let-bindR : ∀ {A A' B B'}{RA : WRel A A'}{RB : WRel B B'} w x y (f : A → B) g →
  LetLiftR RA w x y →
  (∀ w' (ρ : w' ⇒w w) a b → RA w' a b → LetLiftR RB w' (f a) (g (w' .ctxt) (ρ .ren) b)) →
  LetLiftR RB w (f x) (bind-let y g)
let-bindR w x (return y) f g r-xy r-fg = r-fg w id-w x y r-xy
let-bindR w x (if e y₁ y₂) f g r-xy r-fg with eval-ConstraintExp e (w .env)
... | true  = let-bindR w x y₁ f g r-xy r-fg
... | false = let-bindR w x (y₂ (λ x → x)) f g r-xy r-fg
let-bindR w x (let-exp e y) f g r-xy r-fg =
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
  -- FIXME: need preservation of context relatedness under world changes
  λ w' ρ x y x-y → ⟦ t ⟧tm w' ({!!} , x-y)
⟦ s ∙ t ⟧tm w {γₛ}{γₙ} γ₁-γ₂ =
  let-bindR w (S.⟦ s ⟧tm γₛ) (N.⟦ s ⟧tm γₙ)
    _ -- (λ a → a (S.⟦ t ⟧tm γₛ))
    _
    (⟦ s ⟧tm w γ₁-γ₂)
    λ w' ρ a b r-ab →
      let-bindR w' (S.⟦ t ⟧tm γₛ) (N.⟦ t ⟧tm (N.rename-ctxt (ρ .ren) γₙ))
        _ -- (λ a' → a a')
        _
        (⟦ t ⟧tm w' {!!})
        r-ab
⟦ const x ⟧tm w γ₁-γ₂ = refl
⟦ lift t ⟧tm w {γₛ}{γₙ} γ₁-γ₂ =
  let-bindR w (S.⟦ t ⟧tm γₛ) (N.⟦ t ⟧tm γₙ)
   (λ a → a)
   (λ _ _ q → return (const q))
   (⟦ t ⟧tm w γ₁-γ₂)
   λ w' ρ a b a≡b → a≡b
⟦ s `+ t ⟧tm w {γₛ}{γₙ} γ₁-γ₂ =
  let-bindR w (S.⟦ s ⟧tm γₛ) (N.⟦ s ⟧tm γₙ)
    (λ a → a + S.⟦ t ⟧tm γₛ)
    _
    (⟦ s ⟧tm w γ₁-γ₂)
    λ w' ρ a b r-ab →
      let-bindR w' (S.⟦ t ⟧tm γₛ) (N.⟦ t ⟧tm (N.rename-ctxt (ρ .ren) γₙ))
        (λ b → a + b)
        _
        (⟦ t ⟧tm w' {!!}) -- FIXME: context relatedness preserved under extension
        {!!} -- FIXME: preservation of evaluation
⟦ s `* t ⟧tm w γ₁-γ₂ = {!!}
⟦ s `≤ t ⟧tm w γ₁-γ₂ = {!!}
⟦ if s then t else u ⟧tm w {γₛ}{γₙ} γ₁-γ₂ =
  let-bindR w (S.⟦ s ⟧tm γₛ) (N.⟦ s ⟧tm γₙ)
    (λ a → ifᵇ a then S.⟦ t ⟧tm γₛ else S.⟦ u ⟧tm γₛ)
    _
    (⟦ s ⟧tm w γ₁-γ₂)
    r
  where r : ∀ w' (ρ : w' ⇒w w) a b →
            ⟦ Bool constraint ⟧ty w' a b →
            LetLiftR ⟦ _ ⟧ty w'
              (ifᵇ a then S.⟦ t ⟧tm γₛ else S.⟦ u ⟧tm γₛ)
              (if b (N.⟦ t ⟧tm (N.rename-ctxt (ρ .ren) γₙ))
                    (λ ρ' → N.⟦ u ⟧tm (N.rename-ctxt (ρ .ren ∘ ρ') γₙ)))
        r w' ρ false b eq rewrite sym eq = ⟦ u ⟧tm w' {!!}
        r w' ρ true b eq rewrite sym eq = ⟦ t ⟧tm w' {!!}
⟦ `¬ t ⟧tm w {γₛ}{γₙ} γ₁-γ₂ =
  let-bindR w (S.⟦ t ⟧tm γₛ) (N.⟦ t ⟧tm γₙ)
    not
    (λ _ _ x → return (negate x))
    (⟦ t ⟧tm w γ₁-γ₂)
    λ { w' ρ a b refl → {!!} } -- FIXME: negate works correctly
⟦ t `∧ t₁ ⟧tm w γ₁-γ₂ = {!!}
⟦ t `∨ t₁ ⟧tm w γ₁-γ₂ = {!!}
  -- FIXME: lemmas for unary and binary operators
  -- FIXME: would be easier to uncurry and have a lift2 operation:
  ---   lift2 : (A × B ⇒ₖ C) → LetLift A → LetLift B → LetLift C
