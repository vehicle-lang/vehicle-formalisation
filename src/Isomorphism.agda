{-# OPTIONS --postfix-projections #-}

module Isomorphism where

open import Data.Bool renaming (T to True)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

-- FIXME: move this
postulate
  fext : ∀ {ℓ₁ ℓ₂}{A : Set ℓ₁}{B : A → Set ℓ₂}{f g : (a : A) → B a} →
         ((a : A) → f a ≡ g a) → f ≡ g

module _ {ℓ} where

  record _↔_ (A B : Set ℓ) : Set ℓ where
    field
      fwd : A → B
      bwd : B → A
      -- fwd∘bwd : ∀ b → fwd (bwd b) ≡ b
      -- bwd∘fwd : ∀ a → bwd (fwd a) ≡ a
  open _↔_ public

  ↔-refl : ∀ {A} → A ↔ A
  ↔-refl .fwd = λ a → a
  ↔-refl .bwd = λ a → a
  -- ↔-refl .fwd∘bwd a = refl
  -- ↔-refl .bwd∘fwd a = refl

  ↔-trans : ∀ {A B C} → A ↔ B → B ↔ C → A ↔ C
  ↔-trans i₁ i₂ .fwd a = i₂ .fwd (i₁ .fwd a)
  ↔-trans i₁ i₂ .bwd c = i₁ .bwd (i₂ .bwd c)

  cong-→ : ∀ {A₁ A₂ B₁ B₂} →
           A₁ ↔ A₂ → B₁ ↔ B₂ →
           (A₁ → B₁) ↔ (A₂ → B₂)
  cong-→ eq-A eq-B .fwd f a₂ = eq-B .fwd (f (eq-A .bwd a₂))
  cong-→ eq-A eq-B .bwd f a₁ = eq-B .bwd (f (eq-A .fwd a₁))
  -- cong-→ eq-A eq-B .fwd∘bwd f = fext (λ a → trans (eq-B .fwd∘bwd _) (cong f (eq-A .fwd∘bwd a)))
  -- cong-→ eq-A eq-B .bwd∘fwd f = fext (λ a → trans (eq-B .bwd∘fwd _) (cong f (eq-A .bwd∘fwd a)))

  cong-Σ-snd : ∀ {A : Set ℓ}{B₁ B₂ : A → Set ℓ} →
               ((a : A) → B₁ a ↔ B₂ a) →
               (Σ A B₁) ↔ Σ A B₂
  cong-Σ-snd eq .fwd (a , b₁) = a , eq a .fwd b₁
  cong-Σ-snd eq .bwd (a , b₂) = a , eq a .bwd b₂

  known : ∀ {A : Set ℓ}{B : A → Set ℓ} a →
          B a ↔ (Σ[ a' ∈ A ] (a' ≡ a × B a'))
  known a .fwd b = a , refl , b
  known a .bwd (a , refl , b) = b

  cong-Π : ∀ {A : Set ℓ}{B₁ B₂ : A → Set ℓ} →
         ((a : A) → B₁ a ↔ B₂ a) →
         ((a : A) → B₁ a) ↔ ((a : A) → B₂ a)
  cong-Π eq .fwd b₁ a = eq a .fwd (b₁ a)
  cong-Π eq .bwd b₂ a = eq a .bwd (b₂ a)
  -- cong-Π eq .fwd∘bwd b₂ = fext (λ a → eq a .fwd∘bwd (b₂ a))
  -- cong-Π eq .bwd∘fwd b₁ = fext (λ a → eq a .bwd∘fwd (b₁ a))

  cong-F : ∀ {ℓ'} {A : Set ℓ'}(B : A → Set ℓ){a₁ a₂ : A} →
           a₁ ≡ a₂ →
           B a₁ ↔ B a₂
  cong-F B refl = ↔-refl

  or-left : ∀ {A : Set ℓ} → A ↔ (A ⊎ ⊥)
  or-left .fwd = inj₁
  or-left .bwd (inj₁ x) = x

  or-right : ∀ {A : Set ℓ} → A ↔ (⊥ ⊎ A)
  or-right .fwd = inj₂
  or-right .bwd (inj₂ a) = a

  ⊤-fst : ∀ {A : Set ℓ} → A ↔ (⊤ × A)
  ⊤-fst .fwd a = tt , a
  ⊤-fst .bwd (tt , a) = a

⊥-fst : ∀ {A : Set} → ⊥ ↔ (⊥ × A)
⊥-fst .fwd ()
⊥-fst .bwd ()

⊎-cong : ∀ {a b} {A C : Set a}{B D : Set b} → A ↔ C → B ↔ D → (A ⊎ B) ↔ (C ⊎ D)
⊎-cong ac bd .fwd (inj₁ x) = inj₁ (ac .fwd x)
⊎-cong ac bd .fwd (inj₂ y) = inj₂ (bd .fwd y)
⊎-cong ac bd .bwd (inj₁ x) = inj₁ (ac .bwd x)
⊎-cong ac bd .bwd (inj₂ y) = inj₂ (bd .bwd y)

cong-True : ∀ {b₁ b₂ : Bool} → b₁ ≡ b₂ → True b₁ ↔ True b₂
cong-True refl = ↔-refl
