{-# OPTIONS --postfix-projections --allow-unsolved-metas #-}

module NormalisationCorrect where

open import Level using (Lift; lift; lower)
open import Data.Bool using (not; _∧_; _∨_; true; false)
                   renaming (Bool to 𝔹; if_then_else_ to ifᵇ_then_else_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Rational using (ℚ; _+_; _*_; _≤ᵇ_; _≟_)
open import Data.Rational.Properties using (*-identityˡ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (does)

open import MiniVehicle renaming (_⇒ᵣ_ to _⇒K_)
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

wk-w : ∀ {w q} → extend-w w q ⇒w w
wk-w .ren = succ
wk-w .presv x = refl

------------------------------------------------------------------------------

WRel : Set → (LinVarCtxt → Set) → Set₁
WRel A B = ∀ (w : World) → A → B (w .ctxt) → Set

module _ (extFunc : ℚ → ℚ) where

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
  LetLiftR : ∀ {A B} → WRel A B → WRel A (LetLift B)
  LetLiftR R w a (return b) = R w a b
  LetLiftR R w a (if c k₁ k₂) =
    ifᵇ (eval-ConstraintExp extFunc c (w .env))
     then LetLiftR R w a k₁
     else LetLiftR R w a k₂
  LetLiftR R w a (let-linexp e k) =
    LetLiftR R (extend-w w (eval-LinExp e (w .env))) a k
  LetLiftR R w a (let-funexp x k) =
    LetLiftR R (extend-w w (extFunc (w .env x))) a k

  ext-lift : ∀ {A B} {R : WRel A B} →
             (ren-B : ∀ {Δ₁ Δ₂} (ρ : Δ₂ ⇒ᵣ Δ₁) → B Δ₁ → B Δ₂) →
             (∀ {w₁ w₂} (ρ : w₂ ⇒w w₁) {a b} → R w₁ a b → R w₂ a (ren-B (ρ .ren) b)) →
             ∀ {w₁ w₂} (ρ : w₂ ⇒w w₁) la lb →
             LetLiftR R w₁ la lb →
             LetLiftR R w₂ la (rename-lift ren-B (ρ .ren) lb)
  ext-lift ren-B ext-R ρ a (return b) = ext-R ρ
  ext-lift ren-B ext-R {w₁} ρ a (if c tru fal) rewrite sym (ext-evalConstraint c ρ) with eval-ConstraintExp extFunc c (w₁ .env)
  ... | false = ext-lift ren-B ext-R ρ a fal
  ... | true  = ext-lift ren-B ext-R ρ a tru
  ext-lift ren-B ext-R ρ a (let-linexp x lb) =
    ext-lift ren-B ext-R (record { ren = NormalisedExpr.under (ρ .ren) ; presv = λ { zero → sym (ext-evalLinExp x ρ) ; (succ x₁) → ρ .presv x₁ } }) a lb
  ext-lift ren-B ext-R ρ a (let-funexp x lb) =
    ext-lift ren-B ext-R (record { ren = NormalisedExpr.under (ρ .ren) ; presv = λ { zero → cong extFunc (ρ .presv x) ; (succ x₁) → ρ .presv x₁ } }) a lb

  let-bindR : ∀ {A A' B B'}{RA : WRel A A'}{RB : WRel B B'} w x y
    (f : A → B)
    (g : (A' ⇒ₖ LetLift B') (w .ctxt)) →
    LetLiftR RA w x y →
    (∀ w' (ρ : w' ⇒w w) a b → RA w' a b → LetLiftR RB w' (f a) (g (w' .ctxt) (ρ .ren) b)) →
    LetLiftR RB w (f x) (bind-let y g)
  let-bindR w x (return y) f g r-xy r-fg = r-fg w id-w x y r-xy
  let-bindR w x (if e y₁ y₂) f g r-xy r-fg with eval-ConstraintExp extFunc e (w .env)
  ... | true  = let-bindR w x y₁ f g r-xy r-fg
  ... | false = let-bindR w x y₂ f g r-xy r-fg
  let-bindR w x (let-linexp e y) f g r-xy r-fg =
    let-bindR
      (extend-w w (eval-LinExp e (w .env)))
      x
      y
      f
      (λ Δ' ρ a' → g Δ' (λ x₁ → ρ (succ x₁)) a')
      r-xy
      λ w' ρ a b r-ab → r-fg w' (wk-w ∘w ρ) a b r-ab
  let-bindR w x (let-funexp v y) f g r-xy r-fg =
    let-bindR
      (extend-w w (extFunc (w .env v)))
      x
      y
      f
      (λ Δ' ρ a' → g Δ' (λ x₁ → ρ (succ x₁)) a')
      r-xy
      λ w' ρ a b r-ab → r-fg w' (wk-w ∘w ρ) a b r-ab

  ------------------------------------------------------------------------------
  ⟦_⟧kind : (κ : Kind) → S.⟦ κ ⟧kind → N.⟦ κ ⟧kind → Set₁
  ⟦ Nat ⟧kind  x y = Lift _ (x .lower ≡ y .lower)
  ⟦ Type ⟧kind = WRel

  ⟦_⟧kctxt : (Δ : KindContext) → S.⟦ Δ ⟧kctxt → N.⟦ Δ ⟧kctxt → Set
  ⟦ ε ⟧kctxt tt tt = ⊤
  ⟦ Δ ,-ℕ ⟧kctxt (δ₁ , n₁) (δ₂ , n₂) = (⟦ Δ ⟧kctxt δ₁ δ₂) × (n₁ ≡ n₂)

  ⟦_⟧tyvar : ∀ {Δ} (x : Δ ⊢Tv) →
             ∀ {δ₁ δ₂} → ⟦ Δ ⟧kctxt δ₁ δ₂ → ⟦ Nat ⟧kind (S.⟦ x ⟧tyvar δ₁) (N.⟦ x ⟧tyvar δ₂)
  ⟦ zero ⟧tyvar δ₁-δ₂ = lift (δ₁-δ₂ .proj₂)
  ⟦ succ x ⟧tyvar δ₁-δ₂ = ⟦ x ⟧tyvar (δ₁-δ₂ .proj₁)

  ⟦_⟧ty : ∀ {Δ κ} (A : Δ ⊢T κ) →
         ∀ {δ₁ δ₂} → ⟦ Δ ⟧kctxt δ₁ δ₂ → ⟦ κ ⟧kind (S.⟦ A ⟧ty δ₁) (N.⟦ A ⟧ty δ₂)
  ⟦ var x ⟧ty = ⟦ x ⟧tyvar
  ⟦ Bool constraint ⟧ty δ₁-δ₂ w x y = x ≡ eval-ConstraintExp extFunc y (w .env)
  ⟦ Num const ⟧ty       δ₁-δ₂ w x y = x ≡ y
  ⟦ Num linear ⟧ty      δ₁-δ₂ w x y = x ≡ eval-LinExp y (w .env)
  ⟦ A ⇒ B ⟧ty          δ₁-δ₂ w f g =
    ∀ w' (ρ : w' ⇒w w) x y →
      ⟦ A ⟧ty δ₁-δ₂ w' x y →
      LetLiftR (⟦ B ⟧ty δ₁-δ₂) w' (f x) (g (w' .ctxt) (ρ .ren) y)
  ⟦ Array n A ⟧ty       δ₁-δ₂ w a₁ a₂ =
    ∀ idx₁ idx₂ → subst Fin (⟦ n ⟧ty δ₁-δ₂ .lower) idx₁ ≡ idx₂ →
                  LetLiftR (⟦ A ⟧ty δ₁-δ₂) w (a₁ idx₁) (a₂ idx₂)
  ⟦ Index n ⟧ty δ₁-δ₂ w idx₁ idx₂ =
    subst Fin (⟦ n ⟧ty δ₁-δ₂ .lower) idx₁ ≡ idx₂
  ⟦ Forall A ⟧ty K₁-K₂ w x y = (n : ℕ) → LetLiftR (⟦ A ⟧ty (K₁-K₂ , refl)) w (x n) (y n)

  ext-ty : ∀ {Δ} (A : Δ ⊢T Type) {δ₁ δ₂} →
           (δ₁-δ₂ : ⟦ Δ ⟧kctxt δ₁ δ₂) →
           ∀ {w₁ w₂} → (ρ : w₂ ⇒w w₁) → ∀ {x y} →
           ⟦ A ⟧ty δ₁-δ₂ w₁ x y →
           ⟦ A ⟧ty δ₁-δ₂ w₂ x (N.rename-ty A δ₂ (ρ .ren) y)
  ext-ty (Bool constraint) δ₁-δ₂ ρ {x}{y} r =
    trans r (ext-evalConstraint y ρ)
  ext-ty (Num const) δ₁-δ₂ ρ r = r
  ext-ty (Num linear) δ₁-δ₂ ρ {x}{y} r = trans r (ext-evalLinExp y ρ)
  ext-ty (A ⇒ B) δ₁-δ₂ ρ r =
    λ w₃ ρ₁ x₁ y₁ r₂ → r w₃ (ρ ∘w ρ₁) x₁ y₁ r₂
  ext-ty (Array n A) {δ₁}{δ₂} δ₁-δ₂ ρ {x}{y} r =
    λ idx₁ idx₂ idx₁-idx₂ →
       ext-lift (N.rename-ty A δ₂) (ext-ty A δ₁-δ₂) ρ
           (x idx₁) (y idx₂) (r idx₁ idx₂ idx₁-idx₂)
  ext-ty (Index n) δ₁-δ₂ ρ refl = refl
  ext-ty (Forall A) {δ₁}{δ₂} δ₁-δ₂ ρ {x}{y} r n =
    ext-lift (N.rename-ty A (δ₂ , n)) (ext-ty A (δ₁-δ₂ , refl)) ρ (x n) (y n) (r n)

  -- Relatedness for contexts
  ⟦_⟧ctxt : ∀ {Δ} (Γ : Context Δ) {δ₁ δ₂} → ⟦ Δ ⟧kctxt δ₁ δ₂ → WRel (S.⟦ Γ ⟧ctxt δ₁) (N.⟦ Γ ⟧ctxt δ₂)
  ⟦ ε ⟧ctxt      δ₁-δ₂ w tt      tt       = ⊤
  ⟦ Γ ,- A ⟧ctxt δ₁-δ₂ w (γₛ , x) (γₙ , y) = ⟦ Γ ⟧ctxt δ₁-δ₂ w γₛ γₙ × ⟦ A ⟧ty δ₁-δ₂ w x y

  ext-ctxt : ∀ {Δ} (Γ : Context Δ) {δ₁ δ₂} →
             (δ₁-δ₂ : ⟦ Δ ⟧kctxt δ₁ δ₂) →
             ∀ {w₁ w₂} (ρ : w₂ ⇒w w₁) → ∀ {x y} →
             ⟦ Γ ⟧ctxt δ₁-δ₂ w₁ x y →
             ⟦ Γ ⟧ctxt δ₁-δ₂ w₂ x (N.rename-ctxt δ₂ (ρ .ren) y)
  ext-ctxt ε δ₁-δ₂ ρ r = tt
  ext-ctxt (Γ ,- A) δ₁-δ₂ ρ (γ₁γ₂ , a₁a₂) =
    (ext-ctxt Γ δ₁-δ₂ ρ γ₁γ₂) , (ext-ty A δ₁-δ₂ ρ a₁a₂)


  -- Variables' interpretations are related
  ⟦_⟧var : ∀ {Δ Γ A} (x : Δ ⊢ Γ ∋ A)
             {δ₁ δ₂} (δ₁-δ₂ : ⟦ Δ ⟧kctxt δ₁ δ₂) w {γₛ γₙ} →
          ⟦ Γ ⟧ctxt δ₁-δ₂ w γₛ γₙ →
          ⟦ A ⟧ty δ₁-δ₂ w (S.⟦ x ⟧var δ₁ γₛ) (N.⟦ x ⟧var δ₂ γₙ)
  ⟦ zero ⟧var   δ₁-δ₂ w (_    , x-y) = x-y
  ⟦ succ x ⟧var δ₁-δ₂ w (γₛ-γₙ , _  ) = ⟦ x ⟧var δ₁-δ₂ w γₛ-γₙ

  module ST = S.TermSem (extFunc)

  -- Terms' interpretations are related
  ⟦_⟧tm : ∀ {Δ Γ A} (x : Δ / Γ ⊢ A) {δ₁ δ₂} (δ₁-δ₂ : ⟦ Δ ⟧kctxt δ₁ δ₂) w {γₛ γₙ} →
          ⟦ Γ ⟧ctxt δ₁-δ₂ w γₛ γₙ →
          LetLiftR (⟦ A ⟧ty δ₁-δ₂) w (ST.⟦ x ⟧tm δ₁ γₛ) (N.⟦ x ⟧tm δ₂ γₙ)
  ⟦ var x ⟧tm δ₁-δ₂ w γ₁-γ₂ = ⟦ x ⟧var δ₁-δ₂ w γ₁-γ₂
  ⟦ ƛ t ⟧tm δ₁-δ₂ w γ₁-γ₂ =
    λ w' ρ x y x-y → ⟦ t ⟧tm δ₁-δ₂ w' (ext-ctxt _ δ₁-δ₂ ρ γ₁-γ₂ , x-y)
  ⟦ s ∙ t ⟧tm δ₁-δ₂ w {γₛ}{γₙ} γ₁-γ₂ =
    let-bindR w (ST.⟦ s ⟧tm _ γₛ) (N.⟦ s ⟧tm _ γₙ)
      _ -- (λ a → a (S.⟦ t ⟧tm γₛ))
      _
      (⟦ s ⟧tm δ₁-δ₂ w γ₁-γ₂)
      λ w' ρ a b r-ab →
        let-bindR w' (ST.⟦ t ⟧tm _ γₛ) (N.⟦ t ⟧tm _ (N.rename-ctxt _ (ρ .ren) γₙ))
          _ -- (λ a' → a a')
          _
          (⟦ t ⟧tm δ₁-δ₂ w' (ext-ctxt _ δ₁-δ₂ ρ γ₁-γ₂))
          r-ab
  ⟦ Λ t ⟧tm δ₁-δ₂ w {γₛ}{γₙ} γₛ-γₙ =
    λ n → ⟦ t ⟧tm (δ₁-δ₂ , refl) w {!!}
  ⟦ _•_ {A = A} t N ⟧tm δ₁-δ₂ w {γₛ}{γₙ} γₛ-γₙ =
    {!!}

  -- Uninterpreted Functions
  ⟦ func t ⟧tm δ₁-δ₂ w {γₛ}{γₙ} γ₁-γ₂ =
    let-bindR w (ST.⟦ t ⟧tm _ γₛ) (N.⟦ t ⟧tm _ γₙ)
      extFunc
      _
      (⟦ t ⟧tm δ₁-δ₂ w γ₁-γ₂)
      λ { w' ρ a b refl → sym (*-identityˡ _) }

  ⟦ const x ⟧tm δ₁-δ₂ w γ₁-γ₂ = refl
  ⟦ lift t ⟧tm δ₁-δ₂ w {γₛ}{γₙ} γ₁-γ₂ =
    let-bindR w (ST.⟦ t ⟧tm _ γₛ) (N.⟦ t ⟧tm _ γₙ)
     (λ a → a)
     (λ _ _ q → return (const q))
     (⟦ t ⟧tm δ₁-δ₂ w γ₁-γ₂)
     λ w' ρ a b a≡b → a≡b

  ⟦ s `+ t ⟧tm δ₁-δ₂ w {γₛ}{γₙ} γ₁-γ₂ =
    let-bindR w (ST.⟦ s ⟧tm _ γₛ) (N.⟦ s ⟧tm _ γₙ)
      (λ a → a + ST.⟦ t ⟧tm _ γₛ)
      _
      (⟦ s ⟧tm δ₁-δ₂ w γ₁-γ₂)
      λ w' ρ a b r-ab →
        let-bindR w' (ST.⟦ t ⟧tm _ γₛ) (N.⟦ t ⟧tm _ (N.rename-ctxt _ (ρ .ren) γₙ))
          (λ b → a + b)
          _
          (⟦ t ⟧tm δ₁-δ₂ w' (ext-ctxt _ δ₁-δ₂ ρ γ₁-γ₂))
          λ w'' ρ₁ a₁ b₁ r-a₁b₁ →
            cong₂ _+_ (trans r-ab (ext-evalLinExp b ρ₁)) r-a₁b₁
  ⟦ s `* t ⟧tm δ₁-δ₂ w {γₛ}{γₙ} γ₁-γ₂ =
    let-bindR w (ST.⟦ s ⟧tm _ γₛ) (N.⟦ s ⟧tm _ γₙ)
      (λ a → a * ST.⟦ t ⟧tm _ γₛ)
      _
      (⟦ s ⟧tm δ₁-δ₂ w γ₁-γ₂)
      λ w' ρ a b r-ab →
        let-bindR w' (ST.⟦ t ⟧tm _ γₛ) (N.⟦ t ⟧tm _ (N.rename-ctxt _ (ρ .ren) γₙ))
          (λ b → a * b)
          _
          (⟦ t ⟧tm δ₁-δ₂ w' (ext-ctxt _ δ₁-δ₂ ρ γ₁-γ₂))
          λ w'' ρ₁ a₁ b₁ r-a₁b₁ →
            trans (cong₂ _*_ r-ab r-a₁b₁)
                  (eval-⊛ b b₁ (w'' .env))
  ⟦ array n A t ⟧tm δ₁-δ₂ w {γₛ}{γₙ} γₛ-γₙ =
    -- FIXME: this will have to change if the Lifting behaviour of arrays changes
    λ idx₁ idx₂ eq-idx → ⟦ t ⟧tm δ₁-δ₂ w (γₛ-γₙ , eq-idx)
  ⟦ index n A s t ⟧tm {δ₁}{δ₂} δ₁-δ₂ w {γₛ}{γₙ} γₛ-γₙ =
    let-bindR w (ST.⟦ s ⟧tm _ γₛ) (N.⟦ s ⟧tm _ γₙ)
      _ _
      (⟦ s ⟧tm δ₁-δ₂ w γₛ-γₙ)
      λ w' ρ arr₁ arr₂ arr₁-arr₂ →
      let-bindR w' (ST.⟦ t ⟧tm _ γₛ) (N.⟦ t ⟧tm _ (N.rename-ctxt _ (ρ .ren) γₙ))
        arr₁
        _
        (⟦ t ⟧tm δ₁-δ₂ w' (ext-ctxt _ δ₁-δ₂ ρ γₛ-γₙ))
        λ w'' ρ' a b r-ab →
          ext-lift (N.rename-ty A δ₂) (ext-ty A δ₁-δ₂)
            ρ'
            (arr₁ a)
            (arr₂ b)
            (arr₁-arr₂ a b r-ab)

  ⟦ s `≤ t ⟧tm δ₁-δ₂ w {γₛ}{γₙ} γ₁-γ₂ =
    let-bindR w (ST.⟦ s ⟧tm _ γₛ) (N.⟦ s ⟧tm _ γₙ)
      (λ a → a ≤ᵇ ST.⟦ t ⟧tm _ γₛ)
      _
      (⟦ s ⟧tm δ₁-δ₂ w γ₁-γ₂)
      λ w' ρ a b r-ab →
        let-bindR w' (ST.⟦ t ⟧tm _ γₛ) (N.⟦ t ⟧tm _ (N.rename-ctxt _ (ρ .ren) γₙ))
          (λ b → a ≤ᵇ b)
          _
          (⟦ t ⟧tm δ₁-δ₂ w' (ext-ctxt _ δ₁-δ₂ ρ γ₁-γ₂))
          λ w'' ρ₁ a₁ b₁ r-a₁b₁ →
            cong₂ _≤ᵇ_ (trans r-ab (ext-evalLinExp b ρ₁)) r-a₁b₁
  ⟦_⟧tm {A = A} (if s then t else u) {δ₂ = δ₂} δ₁-δ₂ w {γₛ}{γₙ} γ₁-γ₂ =
    let-bindR w (ST.⟦ s ⟧tm _ γₛ) (N.⟦ s ⟧tm _ γₙ)
      (λ a → ifᵇ a then ST.⟦ t ⟧tm _ γₛ else ST.⟦ u ⟧tm _ γₛ)
      _
      (⟦ s ⟧tm δ₁-δ₂ w γ₁-γ₂)
      r
    where r : ∀ w' (ρ : w' ⇒w w) a b →
              ⟦ Bool constraint ⟧ty δ₁-δ₂ w' a b →
              LetLiftR (⟦ A ⟧ty δ₁-δ₂) w'
                (ifᵇ a then ST.⟦ t ⟧tm _ γₛ else ST.⟦ u ⟧tm _ γₛ)
                (if b (N.⟦ t ⟧tm δ₂ (N.rename-ctxt δ₂ (ρ .ren) γₙ))
                      (N.⟦ u ⟧tm δ₂ (N.rename-ctxt δ₂ (ρ .ren) γₙ)))
          r w' ρ false b eq rewrite sym eq = ⟦ u ⟧tm δ₁-δ₂ w' (ext-ctxt _ δ₁-δ₂ ρ γ₁-γ₂)
          r w' ρ true b eq rewrite sym eq = ⟦ t ⟧tm δ₁-δ₂ w' (ext-ctxt _ δ₁-δ₂ ρ γ₁-γ₂)
  ⟦ `¬ t ⟧tm δ₁-δ₂ w {γₛ}{γₙ} γ₁-γ₂ =
    let-bindR w (ST.⟦ t ⟧tm _ γₛ) (N.⟦ t ⟧tm _ γₙ)
      not
      (λ _ _ x → return (negate x))
      (⟦ t ⟧tm δ₁-δ₂ w γ₁-γ₂)
      λ { w' ρ a b refl → eval-negate extFunc b (w' .env) }
  ⟦ s `∧ t ⟧tm δ₁-δ₂ w {γₛ}{γₙ} γ₁-γ₂ =
    let-bindR w (ST.⟦ s ⟧tm _ γₛ) (N.⟦ s ⟧tm _ γₙ)
      (λ a → a ∧ ST.⟦ t ⟧tm _ γₛ)
      _
      (⟦ s ⟧tm δ₁-δ₂ w γ₁-γ₂)
      λ w' ρ a b r-ab →
        let-bindR w' (ST.⟦ t ⟧tm _ γₛ) (N.⟦ t ⟧tm _ (N.rename-ctxt _ (ρ .ren) γₙ))
          (λ b → a ∧ b)
          _
          (⟦ t ⟧tm δ₁-δ₂ w' (ext-ctxt _ δ₁-δ₂ ρ γ₁-γ₂))
          λ w'' ρ₁ a₁ b₁ r-a₁b₁ →
          cong₂ _∧_ (trans r-ab (ext-evalConstraint b ρ₁)) r-a₁b₁
  ⟦ s `∨ t ⟧tm δ₁-δ₂ w {γₛ}{γₙ} γ₁-γ₂ =
    let-bindR w (ST.⟦ s ⟧tm _ γₛ) (N.⟦ s ⟧tm _ γₙ)
      (λ a → a ∨ ST.⟦ t ⟧tm _ γₛ)
      _
      (⟦ s ⟧tm δ₁-δ₂ w γ₁-γ₂)
      λ w' ρ a b r-ab →
        let-bindR w' (ST.⟦ t ⟧tm _ γₛ) (N.⟦ t ⟧tm _ (N.rename-ctxt _ (ρ .ren) γₙ))
          (λ b → a ∨ b)
          _
          (⟦ t ⟧tm δ₁-δ₂ w' (ext-ctxt _ δ₁-δ₂ ρ γ₁-γ₂))
          λ w'' ρ₁ a₁ b₁ r-a₁b₁ →
          cong₂ _∨_ (trans r-ab (ext-evalConstraint b ρ₁)) r-a₁b₁
