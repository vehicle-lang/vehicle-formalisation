{-# OPTIONS --postfix-projections --safe #-}

module Normalisation where

open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.Rational using (ℚ; 1ℚ)
open import Data.Unit using (⊤; tt)
open import MiniVehicle
open import NormalisedExpr

⟦_⟧ty : Type → LinVarCtxt → Set
⟦ Bool constraint ⟧ty = ConstraintExp
⟦ Num const ⟧ty       = K ℚ
⟦ Num linear ⟧ty      = LinExp
⟦ A ⇒ B ⟧ty          = ⟦ A ⟧ty ⇒ₖ LetLift ⟦ B ⟧ty

rename-ty : ∀ A → Renameable ⟦ A ⟧ty
rename-ty (Bool constraint) = rename-ConstraintExp
rename-ty (Num const)       = rename-K
rename-ty (Num linear)      = rename-LinExp
rename-ty (A ⇒ A₁)         = rename-⇒ₖ

⟦_⟧ctxt : Context → LinVarCtxt → Set
⟦ ε ⟧ctxt Δ = ⊤
⟦ Γ ,- A ⟧ctxt Δ = ⟦ Γ ⟧ctxt Δ × ⟦ A ⟧ty Δ

rename-ctxt : ∀ {Γ} → Renameable ⟦ Γ ⟧ctxt
rename-ctxt {ε}      ρ tt      = tt
rename-ctxt {Γ ,- A} ρ (γ , a) = rename-ctxt {Γ} ρ γ , rename-ty A ρ a

⟦_⟧var : ∀ {Γ A} → Γ ∋ A → ∀ {Δ} → ⟦ Γ ⟧ctxt Δ → ⟦ A ⟧ty Δ
⟦ zero ⟧var   (_ , a) = a
⟦ succ x ⟧var (γ , _) = ⟦ x ⟧var γ

⟦_⟧tm : ∀ {Γ A} → Γ ⊢ A → ∀ {Δ} → ⟦ Γ ⟧ctxt Δ → LetLift ⟦ A ⟧ty Δ
⟦ var x ⟧tm γ =
  return (⟦ x ⟧var γ)
⟦ ƛ t ⟧tm γ =
  -- FIXME: if the domain type is 'Num linear', then convert this to a
  -- let expression, to prevent some unnecessary expansion of terms
  return (λ Δ' ρ a → ⟦ t ⟧tm (rename-ctxt ρ γ , a))
⟦ s ∙ t ⟧tm γ =
  bind-let (⟦ s ⟧tm γ) λ Δ' ρ f →
  bind-let (⟦ t ⟧tm (rename-ctxt ρ γ)) λ Δ'' ρ' a →
  f _ ρ' a
⟦ func t ⟧tm γ =
  bind-let (⟦ t ⟧tm γ) λ Δ' ρ e →
  let-linexp e (let-funexp {- f -} zero (return (var 1ℚ zero)))
⟦ const x ⟧tm γ =
  return x
⟦ lift t ⟧tm γ =
  bind-let (⟦ t ⟧tm γ) λ Δ' ρ q →
  return (const q)
⟦ t₁ `+ t₂ ⟧tm γ =
  bind-let (⟦ t₁ ⟧tm γ) λ Δ' ρ e₁ →
  bind-let (⟦ t₂ ⟧tm (rename-ctxt ρ γ)) λ Δ'' ρ' e₂ →
  return (rename-LinExp ρ' e₁ `+ e₂)
⟦ t₁ `* t₂ ⟧tm γ =
  bind-let (⟦ t₁ ⟧tm γ) λ Δ' ρ e₁ →
  bind-let (⟦ t₂ ⟧tm (rename-ctxt ρ γ)) λ Δ'' ρ' e₂ →
  return (e₁ ⊛ e₂)
⟦ t₁ `≤ t₂ ⟧tm γ =
  bind-let (⟦ t₁ ⟧tm γ) λ Δ' ρ e₁ →
  bind-let (⟦ t₂ ⟧tm (rename-ctxt ρ γ)) λ Δ'' ρ' e₂ →
  return (rename-LinExp ρ' e₁ `≤` e₂)
⟦ if s then t else u ⟧tm γ =
  bind-let (⟦ s ⟧tm γ) λ Δ' ρ e →
  if e (⟦ t ⟧tm (rename-ctxt ρ γ)) (λ ρ' → ⟦ u ⟧tm (rename-ctxt (ρ ∘ ρ') γ))
⟦ `¬ t ⟧tm γ =
  bind-let (⟦ t ⟧tm γ) λ Δ' ρ ϕ →
  return (negate ϕ)
⟦ t₁ `∧ t₂ ⟧tm γ =
  bind-let (⟦ t₁ ⟧tm γ) λ Δ' ρ ϕ₁ →
  bind-let (⟦ t₂ ⟧tm (rename-ctxt ρ γ)) λ Δ'' ρ' ϕ₂ →
  return (rename-ConstraintExp ρ' ϕ₁ and ϕ₂)
⟦ t₁ `∨ t₂ ⟧tm γ =
  bind-let (⟦ t₁ ⟧tm γ) λ Δ' ρ ϕ₁ →
  bind-let (⟦ t₂ ⟧tm (rename-ctxt ρ γ)) λ Δ'' ρ' ϕ₂ →
  return (rename-ConstraintExp ρ' ϕ₁ or ϕ₂)

normalise : ε ⊢ Bool constraint → Ex ConstraintExp ε
normalise t = expand (bind-let (⟦ t ⟧tm tt) λ Δ' ρ c → return (return c))
