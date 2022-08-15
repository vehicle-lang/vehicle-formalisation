{-# OPTIONS --postfix-projections --safe #-}

module Normalisation where

open import Level using (Lift; lift)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.Rational using (ℚ; 1ℚ)
open import Data.Unit using (⊤; tt)

open import MiniVehicle
open import NormalisedExpr

⟦_⟧kind : Kind → Set₁
⟦ Nat ⟧kind  = Lift _ ℕ
⟦ Type ⟧kind = LinVarCtxt → Set

⟦_⟧kctxt : KindContext → Set
⟦ ε ⟧kctxt      = ⊤
⟦ Δ ,-ℕ ⟧kctxt = ⟦ Δ ⟧kctxt × ℕ

⟦_⟧ty : ∀ {Δ κ} → Δ ⊢T κ → ⟦ Δ ⟧kctxt → ⟦ κ ⟧kind
⟦ Bool constraint ⟧ty δ = ConstraintExp
⟦ Num const ⟧ty       δ = K ℚ
⟦ Num linear ⟧ty      δ = LinExp
⟦ A ⇒ B ⟧ty          δ = ⟦ A ⟧ty δ ⇒ₖ LetLift (⟦ B ⟧ty δ)

rename-ty : ∀ {Δ} → (A : Δ ⊢T Type) → ∀ δ → Renameable (⟦ A ⟧ty δ)
rename-ty (Bool constraint) δ = rename-ConstraintExp
rename-ty (Num const)       δ = rename-K
rename-ty (Num linear)      δ = rename-LinExp
rename-ty (A ⇒ A₁)         δ = rename-⇒ₖ

⟦_⟧ctxt : ∀ {Δ} → Context Δ → ⟦ Δ ⟧kctxt → LinVarCtxt → Set
⟦ ε ⟧ctxt      δ Δ = ⊤
⟦ Γ ,- A ⟧ctxt δ Δ = ⟦ Γ ⟧ctxt δ Δ × ⟦ A ⟧ty δ Δ


rename-ctxt : ∀ {Δ}{Γ : Context Δ} → ∀ δ → Renameable (⟦ Γ ⟧ctxt δ)
rename-ctxt {_}{ε}      δ ρ tt      = tt
rename-ctxt {_}{Γ ,- A} δ ρ (γ , a) = rename-ctxt {_}{Γ} δ ρ γ , rename-ty A δ ρ a


⟦_⟧var : ∀ {Δ Γ A} → Δ ⊢ Γ ∋ A → ∀ δ → ∀ {Δ} → ⟦ Γ ⟧ctxt δ Δ → ⟦ A ⟧ty δ Δ
⟦ zero ⟧var   δ (_ , a) = a
⟦ succ x ⟧var δ (γ , _) = ⟦ x ⟧var δ γ

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
⟦ t₁ `≤ t₂ ⟧tm δ γ =
  bind-let (⟦ t₁ ⟧tm δ γ) λ Δ' ρ e₁ →
  bind-let (⟦ t₂ ⟧tm δ (rename-ctxt δ ρ γ)) λ Δ'' ρ' e₂ →
  return (rename-LinExp ρ' e₁ `≤` e₂)
⟦ if s then t else u ⟧tm δ γ =
  bind-let (⟦ s ⟧tm δ γ) λ Δ' ρ e →
  if e (⟦ t ⟧tm δ (rename-ctxt δ ρ γ)) (λ ρ' → ⟦ u ⟧tm δ (rename-ctxt δ (ρ ∘ ρ') γ))
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
normalise t = expand (bind-let (⟦ t ⟧tm tt tt) λ Δ' ρ c → return (return c))
