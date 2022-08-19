{-# OPTIONS --postfix-projections #-}

module Normalisation where

open import Level using (Lift; lift; lower)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.Rational using (ℚ; 1ℚ)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)

open import MiniVehicle
open import NormalisedExpr
open import Isomorphism

⟦_⟧kind : Kind → Set₁
⟦ Nat ⟧kind  = Lift _ ℕ
⟦ Type ⟧kind = LinVarCtxt → Set

⟦_⟧kind-Eq : (κ : Kind) → ⟦ κ ⟧kind → ⟦ κ ⟧kind → Set
⟦ Nat ⟧kind-Eq  x y = x .lower ≡ y .lower
⟦ Type ⟧kind-Eq x y = ∀ Δ → x Δ ↔ y Δ -- NOTE: not bothering to show that it is a natural iso

⟦_⟧kctxt : KindContext → Set
⟦ ε ⟧kctxt      = ⊤
⟦ Δ ,-ℕ ⟧kctxt = ⟦ Δ ⟧kctxt × ℕ

⟦_⟧tyvar : ∀ {Δ} → Δ ⊢Tv → ⟦ Δ ⟧kctxt → ⟦ Nat ⟧kind
⟦ zero ⟧tyvar   (_ , n) = lift n
⟦ succ x ⟧tyvar (δ , _) = ⟦ x ⟧tyvar δ

⟦_⟧ty : ∀ {Δ κ} → Δ ⊢T κ → ⟦ Δ ⟧kctxt → ⟦ κ ⟧kind
⟦ var x ⟧ty           δ = ⟦ x ⟧tyvar δ
⟦ Bool constraint ⟧ty δ = ConstraintExp
⟦ Num const ⟧ty       δ = K ℚ
⟦ Num linear ⟧ty      δ = LinExp
⟦ A ⇒ B ⟧ty          δ = ⟦ A ⟧ty δ ⇒ₖ LetLift (⟦ B ⟧ty δ)
⟦ Index n ⟧ty         δ = K (Fin (⟦ n ⟧ty δ .lower))
⟦ Array n A ⟧ty       δ = λ Δ → Fin (⟦ n ⟧ty δ .lower) → LetLift (⟦ A ⟧ty δ) Δ
⟦ Forall A ⟧ty        δ = λ Δ → (n : ℕ) → LetLift (⟦ A ⟧ty (δ , n)) Δ

rename-ty : ∀ {Δ} → (A : Δ ⊢T Type) → ∀ δ → Renameable (⟦ A ⟧ty δ)
rename-ty (Bool constraint) δ = rename-ConstraintExp
rename-ty (Num const)       δ = rename-K
rename-ty (Num linear)      δ = rename-LinExp
rename-ty (A ⇒ B)          δ = rename-⇒ₖ
rename-ty (Index n)         δ = rename-K
rename-ty (Array n A)       δ = λ ρ x idx → rename-lift (rename-ty A δ) ρ (x idx)
rename-ty (Forall A)        δ = λ ρ x n → rename-lift (rename-ty A (δ , n)) ρ (x n)

cong-Lift : ∀ {A₁ A₂} →
            (∀ Δ → A₁ Δ ↔ A₂ Δ) →
            (∀ Δ → LetLift A₁ Δ ↔ LetLift A₂ Δ)
cong-Lift eq Δ .fwd (return x) = return (eq Δ .fwd x)
cong-Lift eq Δ .fwd (if p x₁ x₂) = if p (cong-Lift eq Δ .fwd x₁) (cong-Lift eq Δ .fwd x₂)
cong-Lift eq Δ .fwd (let-linexp x x₁) = let-linexp x (cong-Lift eq (Δ ,∙) .fwd x₁)
cong-Lift eq Δ .fwd (let-funexp x x₁) = let-funexp x (cong-Lift eq (Δ ,∙) .fwd x₁)
cong-Lift eq Δ .bwd (return x) = return (eq Δ .bwd x)
cong-Lift eq Δ .bwd (if p x₁ x₂) = if p (cong-Lift eq Δ .bwd x₁) (cong-Lift eq Δ .bwd x₂)
cong-Lift eq Δ .bwd (let-linexp x x₁) = let-linexp x (cong-Lift eq (Δ ,∙) .bwd x₁)
cong-Lift eq Δ .bwd (let-funexp x x₁) = let-funexp x (cong-Lift eq (Δ ,∙) .bwd x₁)
cong-Lift eq Δ .fwd∘bwd (return x) = cong return (eq Δ .fwd∘bwd x)
cong-Lift eq Δ .fwd∘bwd (if x x₁ x₂) = cong₂ (if x) (cong-Lift eq Δ .fwd∘bwd x₁) (cong-Lift eq Δ .fwd∘bwd x₂)
cong-Lift eq Δ .fwd∘bwd (let-linexp x x₁) = cong (let-linexp x) (cong-Lift eq (Δ ,∙) .fwd∘bwd x₁)
cong-Lift eq Δ .fwd∘bwd (let-funexp x x₁) = cong (let-funexp x) (cong-Lift eq (Δ ,∙) .fwd∘bwd x₁)
cong-Lift eq Δ .bwd∘fwd (return x) = cong return (eq Δ .bwd∘fwd x)
cong-Lift eq Δ .bwd∘fwd (if x x₁ x₂) = cong₂ (if x) (cong-Lift eq Δ .bwd∘fwd x₁) (cong-Lift eq Δ .bwd∘fwd x₂)
cong-Lift eq Δ .bwd∘fwd (let-linexp x x₁) = cong (let-linexp x) (cong-Lift eq (Δ ,∙) .bwd∘fwd x₁)
cong-Lift eq Δ .bwd∘fwd (let-funexp x x₁) = cong (let-funexp x) (cong-Lift eq (Δ ,∙) .bwd∘fwd x₁)

ren-⟦Type⟧ : ∀ {K K' κ} (A : K ⊢T κ) (ρ : K' MiniVehicle.⇒ᵣ K) →
             ∀ {δ δ'} →
             ((x : K ⊢Tv) → ⟦ Nat ⟧kind-Eq (⟦ x ⟧tyvar δ) (⟦ ρ x ⟧tyvar δ')) →
             ⟦ κ ⟧kind-Eq (⟦ A ⟧ty δ) (⟦ ren-Type ρ A ⟧ty δ')
ren-⟦Type⟧ (var x) ρ δ₁-δ₂ = δ₁-δ₂ x
ren-⟦Type⟧ (Bool constraint) ρ δ₁-δ₂ = λ Δ → ↔-refl
ren-⟦Type⟧ (Num const) ρ δ₁-δ₂ = λ Δ → ↔-refl
ren-⟦Type⟧ (Num linear) ρ δ₁-δ₂ = λ Δ → ↔-refl
ren-⟦Type⟧ (A ⇒ B) ρ δ₁-δ₂ = λ Δ →
  cong-Π λ Δ' →
  cong-Π λ ρ' →
  cong-→ (ren-⟦Type⟧ A ρ δ₁-δ₂ Δ')
         (cong-Lift (ren-⟦Type⟧ B ρ δ₁-δ₂) Δ')
ren-⟦Type⟧ (Index N) ρ δ₁-δ₂ = λ Δ → cong-F Fin (ren-⟦Type⟧ N ρ δ₁-δ₂)
ren-⟦Type⟧ (Array N B) ρ δ₁-δ₂ =
  λ Δ → cong-→ (cong-F Fin (ren-⟦Type⟧ N ρ δ₁-δ₂)) (cong-Lift (ren-⟦Type⟧ B ρ δ₁-δ₂) Δ)
ren-⟦Type⟧ (Forall A) ρ δ₁-δ₂ =
  λ Δ → cong-Π (λ n → cong-Lift (ren-⟦Type⟧ A (MiniVehicle.under ρ) λ { zero → refl ; (succ x) → δ₁-δ₂ x }) Δ)

⟦_⟧ctxt : ∀ {K} → Context K → ⟦ K ⟧kctxt → LinVarCtxt → Set
⟦ ε ⟧ctxt      δ Δ = ⊤
⟦ Γ ,- A ⟧ctxt δ Δ = ⟦ Γ ⟧ctxt δ Δ × ⟦ A ⟧ty δ Δ

rename-ctxt : ∀ {K}{Γ : Context K} → ∀ δ → Renameable (⟦ Γ ⟧ctxt δ)
rename-ctxt {_}{ε}      δ ρ tt      = tt
rename-ctxt {_}{Γ ,- A} δ ρ (γ , a) = rename-ctxt {_}{Γ} δ ρ γ , rename-ty A δ ρ a

ren-⟦Context⟧ : ∀ {K K'} (Γ : Context K) (ρ : K' MiniVehicle.⇒ᵣ K) →
                ∀ {δ₁ δ₂} →
                ((x : K ⊢Tv) → ⟦ Nat ⟧kind-Eq (⟦ x ⟧tyvar δ₁) (⟦ ρ x ⟧tyvar δ₂)) →
                ∀ Δ → ⟦ Γ ⟧ctxt δ₁ Δ → ⟦ ren-Context ρ Γ ⟧ctxt δ₂ Δ
ren-⟦Context⟧ ε        ρ δ₁-δ₂ Δ tt = tt
ren-⟦Context⟧ (Γ ,- A) ρ δ₁-δ₂ Δ (γ , x) =
  (ren-⟦Context⟧ Γ ρ δ₁-δ₂ Δ γ) , ren-⟦Type⟧ A ρ δ₁-δ₂ Δ .fwd x

⟦_⟧var : ∀ {Δ Γ A} → Δ ⊢ Γ ∋ A → ∀ δ → ∀ {Δ} → ⟦ Γ ⟧ctxt δ Δ → ⟦ A ⟧ty δ Δ
⟦ zero ⟧var   δ (_ , a) = a
⟦ succ x ⟧var δ (γ , _) = ⟦ x ⟧var δ γ

subst-⟦Type⟧ :
  ∀ {K K' κ} (A : K ⊢T κ) (σ : K ⊢Tv → K' ⊢T Nat) →
  ∀ {δ₁ δ₂} →
  ((x : K ⊢Tv) → ⟦ Nat ⟧kind-Eq (⟦ x ⟧tyvar δ₁) (⟦ σ x ⟧ty δ₂)) →
  ⟦ κ ⟧kind-Eq (⟦ A ⟧ty δ₁) (⟦ subst-Type σ A ⟧ty δ₂)
subst-⟦Type⟧ (var x) σ δ₁-δ₂ = δ₁-δ₂ x
subst-⟦Type⟧ (Bool constraint) σ δ₁-δ₂ = λ Δ → ↔-refl
subst-⟦Type⟧ (Num const) σ δ₁-δ₂ = λ Δ → ↔-refl
subst-⟦Type⟧ (Num linear) σ δ₁-δ₂ = λ Δ → ↔-refl
subst-⟦Type⟧ (A ⇒ B) σ δ₁-δ₂ = λ Δ →
  cong-Π λ Δ' →
  cong-Π λ ρ →
  cong-→ (subst-⟦Type⟧ A σ δ₁-δ₂ Δ')
         (cong-Lift (subst-⟦Type⟧ B σ δ₁-δ₂) Δ')
subst-⟦Type⟧ (Index N) σ δ₁-δ₂ =
  λ Δ → cong-F Fin (subst-⟦Type⟧ N σ δ₁-δ₂)
subst-⟦Type⟧ (Array N A) σ δ₁-δ₂ =
  λ Δ → cong-→ (cong-F Fin (subst-⟦Type⟧ N σ δ₁-δ₂)) (cong-Lift (subst-⟦Type⟧ A σ δ₁-δ₂) Δ)
subst-⟦Type⟧ (Forall A) σ δ₁-δ₂ =
  λ Δ → cong-Π λ n →
        cong-Lift
            (subst-⟦Type⟧ A (binder σ)
               λ { zero → refl
                 ; (succ x) → trans (δ₁-δ₂ x) (ren-⟦Type⟧ (σ x) wk (λ x₁ → refl)) })
            Δ

⟦_⟧tm : ∀ {Δ Γ A} → Δ / Γ ⊢ A → ∀ δ → ∀ {Δ} → ⟦ Γ ⟧ctxt δ Δ → LetLift (⟦ A ⟧ty δ) Δ
⟦ var x ⟧tm δ γ =
  return (⟦ x ⟧var δ γ)
⟦ ƛ t ⟧tm δ γ =
  -- FIXME: if the domain type is 'Num linear', then convert this to a
  -- let expression, to prevent some unnecessary expansion of terms
  return (λ Δ' ρ a → ⟦ t ⟧tm δ (rename-ctxt δ ρ γ , a))
⟦ s ∙ t ⟧tm δ γ =
  bind-let (⟦ s ⟧tm δ γ) λ Δ' ρ f →
  bind-let (⟦ t ⟧tm δ (rename-ctxt δ ρ γ)) λ Δ'' ρ' a →
  f _ ρ' a
⟦ Λ t ⟧tm δ γ =
  return (λ n → ⟦ t ⟧tm (δ , n) (ren-⟦Context⟧ _ wk (λ x → refl) _ γ))
⟦ _•_ {A = A} t N ⟧tm δ γ =
  bind-let (⟦ t ⟧tm δ γ) λ Δ' ρ f →
  bind-let (f (⟦ N ⟧ty δ .lower)) λ Δ'' ρ' a →
  return (subst-⟦Type⟧ A (single-sub N) (λ { zero → refl ; (succ x) → refl }) Δ'' .fwd a)
⟦ func t ⟧tm δ γ =
  bind-let (⟦ t ⟧tm δ γ) λ Δ' ρ e →
  let-linexp e (let-funexp {- f -} zero (return (var 1ℚ zero)))
⟦ const x ⟧tm δ γ =
  return x
⟦ lift t ⟧tm δ γ =
  bind-let (⟦ t ⟧tm δ γ) λ Δ' ρ q →
  return (const q)
⟦ t₁ `+ t₂ ⟧tm δ γ =
  bind-let (⟦ t₁ ⟧tm δ γ) λ Δ' ρ e₁ →
  bind-let (⟦ t₂ ⟧tm δ (rename-ctxt δ ρ γ)) λ Δ'' ρ' e₂ →
  return (rename-LinExp ρ' e₁ `+` e₂)
⟦ t₁ `* t₂ ⟧tm δ γ =
  bind-let (⟦ t₁ ⟧tm δ γ) λ Δ' ρ e₁ →
  bind-let (⟦ t₂ ⟧tm δ (rename-ctxt δ ρ γ)) λ Δ'' ρ' e₂ →
  return (e₁ ⊛ e₂)
⟦ array n A t ⟧tm δ γ =
  -- FIXME: two choices here:
  -- 1. Lazily do the let- and if- lifting so that it gets replicated every time we index
  --    into the array (this is what is implemented here)
  -- 2. Do all the lifting at the creation point, so it gets shared
  --
  -- The difference is manifest in the different possible
  -- implementation types for Array, specifically whether or not it
  -- includes a use of the LetLift monad.
  return (λ idx → ⟦ t ⟧tm δ (γ , idx))
⟦ index n A s t ⟧tm δ γ =
  bind-let (⟦ s ⟧tm δ γ) λ Δ' ρ arr →
  bind-let (⟦ t ⟧tm δ (rename-ctxt δ ρ γ)) λ Δ'' ρ' idx →
  rename-lift (rename-ty A δ) ρ' (arr idx)
⟦ t₁ `≤ t₂ ⟧tm δ γ =
  bind-let (⟦ t₁ ⟧tm δ γ) λ Δ' ρ e₁ →
  bind-let (⟦ t₂ ⟧tm δ (rename-ctxt δ ρ γ)) λ Δ'' ρ' e₂ →
  return (rename-LinExp ρ' e₁ `≤` e₂)
⟦ if s then t else u ⟧tm δ γ =
  bind-let (⟦ s ⟧tm δ γ) λ Δ' ρ e →
  if e (⟦ t ⟧tm δ (rename-ctxt δ ρ γ)) (⟦ u ⟧tm δ (rename-ctxt δ ρ γ))
⟦ `¬ t ⟧tm δ γ =
  bind-let (⟦ t ⟧tm δ γ) λ Δ' ρ ϕ →
  return (negate ϕ)
⟦ t₁ `∧ t₂ ⟧tm δ γ =
  bind-let (⟦ t₁ ⟧tm δ γ) λ Δ' ρ ϕ₁ →
  bind-let (⟦ t₂ ⟧tm δ (rename-ctxt δ ρ γ)) λ Δ'' ρ' ϕ₂ →
  return (rename-ConstraintExp ρ' ϕ₁ and ϕ₂)
⟦ t₁ `∨ t₂ ⟧tm δ γ =
  bind-let (⟦ t₁ ⟧tm δ γ) λ Δ' ρ ϕ₁ →
  bind-let (⟦ t₂ ⟧tm δ (rename-ctxt δ ρ γ)) λ Δ'' ρ' ϕ₂ →
  return (rename-ConstraintExp ρ' ϕ₁ or ϕ₂)

normalise : ε / ε ⊢ Bool constraint → Ex ConstraintExp ε
normalise t = expand (bind-let (⟦ t ⟧tm tt tt) λ Δ' ρ c → return (return c)) (λ x → x)
