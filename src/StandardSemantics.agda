{-# OPTIONS --postfix-projections #-} -- --safe #-}

module StandardSemantics where

open import Level using (Lift; lift; lower)
open import Data.Bool using (true; false; _∧_; _∨_; not)
                   renaming (Bool to 𝔹; if_then_else_ to ifᵇ_then_else_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Rational using (ℚ; _≤ᵇ_) renaming (_+_ to _+ℚ_; _*_ to _*ℚ_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import MiniVehicle
open import Isomorphism

-- FIXME: this needs to be a setoid??? Ought the denotations be
-- setoids too?
⟦_⟧kind : Kind → Set₁
⟦ Nat ⟧kind  = Lift _ ℕ
⟦ Type ⟧kind = Set

⟦_⟧kind-Eq : (κ : Kind) → ⟦ κ ⟧kind → ⟦ κ ⟧kind → Set
⟦ Nat ⟧kind-Eq  x y = x .lower ≡ y .lower
⟦ Type ⟧kind-Eq x y = x ↔ y

⟦_⟧kctxt : KindContext → Set
⟦ ε ⟧kctxt      = ⊤
⟦ K ,-ℕ ⟧kctxt = ⟦ K ⟧kctxt × ℕ

⟦_⟧tyvar : ∀ {K} → K ⊢Tv → ⟦ K ⟧kctxt → ⟦ Nat ⟧kind
⟦ zero ⟧tyvar   (_ , n) = lift n
⟦ succ x ⟧tyvar (δ , _) = ⟦ x ⟧tyvar δ

⟦_⟧ty : ∀ {K κ} → K ⊢T κ → ⟦ K ⟧kctxt → ⟦ κ ⟧kind
⟦ var x ⟧ty           δ = ⟦ x ⟧tyvar δ
⟦ Bool constraint ⟧ty δ = 𝔹
⟦ Num x ⟧ty           δ = ℚ
⟦ A ⇒ B ⟧ty          δ = ⟦ A ⟧ty δ → ⟦ B ⟧ty δ
⟦ Index n ⟧ty         δ = Fin (⟦ n ⟧ty δ .lower)
⟦ Array n A ⟧ty       δ = Fin (⟦ n ⟧ty δ .lower) → ⟦ A ⟧ty δ
⟦ Forall A ⟧ty        δ = (n : ℕ) → ⟦ A ⟧ty (δ , n)

ren-⟦Type⟧ : ∀ {K K' κ} (A : K ⊢T κ) (ρ : K' ⇒ᵣ K) →
             ∀ {δ δ'} →
             ((x : K ⊢Tv) → ⟦ Nat ⟧kind-Eq (⟦ x ⟧tyvar δ) (⟦ ρ x ⟧tyvar δ')) →
             ⟦ κ ⟧kind-Eq (⟦ A ⟧ty δ) (⟦ ren-Type ρ A ⟧ty δ')
ren-⟦Type⟧ (var x) ρ δ₁-δ₂ = δ₁-δ₂ x
ren-⟦Type⟧ (Bool constraint) ρ δ₁-δ₂ = ↔-refl
ren-⟦Type⟧ (Num x) ρ δ₁-δ₂ = ↔-refl
ren-⟦Type⟧ (A ⇒ B) ρ δ₁-δ₂ = cong-→ (ren-⟦Type⟧ A ρ δ₁-δ₂) (ren-⟦Type⟧ B ρ δ₁-δ₂)
ren-⟦Type⟧ (Index N) ρ δ₁-δ₂ = cong-F Fin (ren-⟦Type⟧ N ρ δ₁-δ₂)
ren-⟦Type⟧ (Array N A) ρ δ₁-δ₂ =
  cong-→ (cong-F Fin (ren-⟦Type⟧ N ρ δ₁-δ₂))
         (ren-⟦Type⟧ A ρ δ₁-δ₂)
ren-⟦Type⟧ (Forall A) ρ δ₁-δ₂ =
  cong-Π (λ n → ren-⟦Type⟧ A (under ρ) λ { zero → refl ; (succ x) → δ₁-δ₂ x })



⟦_⟧ctxt : ∀ {K} → Context K → ⟦ K ⟧kctxt → Set
⟦ ε ⟧ctxt      δ = ⊤
⟦ Γ ,- A ⟧ctxt δ = ⟦ Γ ⟧ctxt δ × ⟦ A ⟧ty δ

ren-⟦Context⟧ : ∀ {K K'} (Γ : Context K) (ρ : K' ⇒ᵣ K) →
                ∀ {δ₁ δ₂} →
                ((x : K ⊢Tv) → ⟦ Nat ⟧kind-Eq (⟦ x ⟧tyvar δ₁) (⟦ ρ x ⟧tyvar δ₂)) →
                ⟦ Γ ⟧ctxt δ₁ → ⟦ ren-Context ρ Γ ⟧ctxt δ₂
ren-⟦Context⟧ ε        ρ δ₁-δ₂ tt = tt
ren-⟦Context⟧ (Γ ,- A) ρ δ₁-δ₂ (γ , x) =
  (ren-⟦Context⟧ Γ ρ δ₁-δ₂ γ) , ren-⟦Type⟧ A ρ δ₁-δ₂ .fwd x

⟦_⟧var : ∀ {K Γ A} → K ⊢ Γ ∋ A → ∀ δ → ⟦ Γ ⟧ctxt δ → ⟦ A ⟧ty δ
⟦ zero ⟧var   δ (_ , a) = a
⟦ succ x ⟧var δ (γ , _) = ⟦ x ⟧var δ γ

subst-⟦Type⟧ :
  ∀ {K K' κ} (A : K ⊢T κ) (σ : K ⊢Tv → K' ⊢T Nat) →
  ∀ {δ₁ δ₂} →
  ((x : K ⊢Tv) → ⟦ Nat ⟧kind-Eq (⟦ x ⟧tyvar δ₁) (⟦ σ x ⟧ty δ₂)) →
  ⟦ κ ⟧kind-Eq (⟦ A ⟧ty δ₁) (⟦ subst-Type σ A ⟧ty δ₂)
subst-⟦Type⟧ (var x) σ δ₁-δ₂ = δ₁-δ₂ x
subst-⟦Type⟧ (Bool constraint) σ δ₁-δ₂ = ↔-refl
subst-⟦Type⟧ (Num x) σ δ₁-δ₂ = ↔-refl
subst-⟦Type⟧ (A ⇒ B) σ δ₁-δ₂ = cong-→ (subst-⟦Type⟧ A σ δ₁-δ₂) (subst-⟦Type⟧ B σ δ₁-δ₂)
subst-⟦Type⟧ (Index N) σ δ₁-δ₂ = cong-F Fin (subst-⟦Type⟧ N σ δ₁-δ₂)
subst-⟦Type⟧ (Array N A) σ δ₁-δ₂ =
  cong-→ (cong-F Fin (subst-⟦Type⟧ N σ δ₁-δ₂)) (subst-⟦Type⟧ A σ δ₁-δ₂)
subst-⟦Type⟧ (Forall A) σ δ₁-δ₂ =
  cong-Π (λ n → subst-⟦Type⟧ A (binder σ)
                   λ { zero → refl
                     ; (succ x) → trans (δ₁-δ₂ x) (ren-⟦Type⟧ (σ x) wk λ x₁ → refl) })

module TermSem (f : ℚ → ℚ) where

  ⟦_⟧tm : ∀ {K Γ A} → K / Γ ⊢ A → ∀ δ → ⟦ Γ ⟧ctxt δ → ⟦ A ⟧ty δ
  ⟦ var x ⟧tm δ γ = ⟦ x ⟧var δ γ
  ⟦ ƛ t ⟧tm δ γ = λ a → ⟦ t ⟧tm δ (γ , a)
  ⟦ s ∙ t ⟧tm δ γ = ⟦ s ⟧tm δ γ (⟦ t ⟧tm δ γ)
  ⟦ Λ t ⟧tm δ γ = λ n → ⟦ t ⟧tm (δ , n) (ren-⟦Context⟧ _ wk (λ x → refl) γ)
  ⟦ _•_ {A = A} t N ⟧tm δ γ =
    subst-⟦Type⟧ A (single-sub N) (λ { zero → refl ; (succ x) → refl }) .fwd (⟦ t ⟧tm δ γ (⟦ N ⟧ty δ .lower))

  ⟦ func t ⟧tm δ γ = f (⟦ t ⟧tm δ γ)
  ⟦ const x ⟧tm δ γ = x
  ⟦ lift t ⟧tm δ γ = ⟦ t ⟧tm δ γ
  ⟦ s `+ t ⟧tm δ γ = (⟦ s ⟧tm δ γ) +ℚ (⟦ t ⟧tm δ γ)
  ⟦ s `* t ⟧tm δ γ = (⟦ s ⟧tm δ γ) *ℚ (⟦ t ⟧tm δ γ)

  ⟦ array n A t ⟧tm δ γ = λ idx → ⟦ t ⟧tm δ (γ , idx)
  ⟦ index n A s t ⟧tm δ γ = ⟦ s ⟧tm δ γ (⟦ t ⟧tm δ γ)

  ⟦ s `≤ t ⟧tm δ γ  = (⟦ s ⟧tm δ γ) ≤ᵇ (⟦ t ⟧tm δ γ)
  ⟦ if s then t else u ⟧tm δ γ = ifᵇ (⟦ s ⟧tm δ γ) then (⟦ t ⟧tm δ γ) else (⟦ u ⟧tm δ γ)
  ⟦ `¬ t ⟧tm δ γ = not (⟦ t ⟧tm δ γ)
  ⟦ s `∧ t ⟧tm δ γ = (⟦ s ⟧tm δ γ) ∧ (⟦ t ⟧tm δ γ)
  ⟦ s `∨ t ⟧tm δ γ = (⟦ s ⟧tm δ γ) ∨ (⟦ t ⟧tm δ γ)
