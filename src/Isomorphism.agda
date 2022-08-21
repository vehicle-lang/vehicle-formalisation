{-# OPTIONS --postfix-projections #-}

module Isomorphism where

-- open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

postulate
  fext : ∀ {ℓ₁ ℓ₂}{A : Set ℓ₁}{B : A → Set ℓ₂}{f g : (a : A) → B a} →
         ((a : A) → f a ≡ g a) → f ≡ g

record _↔_ (A B : Set) : Set where
  field
    fwd : A → B
    bwd : B → A
    fwd∘bwd : ∀ b → fwd (bwd b) ≡ b
    bwd∘fwd : ∀ a → bwd (fwd a) ≡ a
open _↔_ public

↔-refl : ∀ {A} → A ↔ A
↔-refl .fwd = λ a → a
↔-refl .bwd = λ a → a
↔-refl .fwd∘bwd a = refl
↔-refl .bwd∘fwd a = refl

cong-→ : ∀ {A₁ A₂ B₁ B₂} →
         A₁ ↔ A₂ → B₁ ↔ B₂ →
         (A₁ → B₁) ↔ (A₂ → B₂)
cong-→ eq-A eq-B .fwd f a₂ = eq-B .fwd (f (eq-A .bwd a₂))
cong-→ eq-A eq-B .bwd f a₁ = eq-B .bwd (f (eq-A .fwd a₁))
cong-→ eq-A eq-B .fwd∘bwd f = fext (λ a → trans (eq-B .fwd∘bwd _) (cong f (eq-A .fwd∘bwd a)))
cong-→ eq-A eq-B .bwd∘fwd f = fext (λ a → trans (eq-B .bwd∘fwd _) (cong f (eq-A .bwd∘fwd a)))

cong-Π : ∀ {A}{B₁ B₂ : A → Set} →
       ((a : A) → B₁ a ↔ B₂ a) →
       ((a : A) → B₁ a) ↔ ((a : A) → B₂ a)
cong-Π eq .fwd b₁ a = eq a .fwd (b₁ a)
cong-Π eq .bwd b₂ a = eq a .bwd (b₂ a)
cong-Π eq .fwd∘bwd b₂ = fext (λ a → eq a .fwd∘bwd (b₂ a))
cong-Π eq .bwd∘fwd b₁ = fext (λ a → eq a .bwd∘fwd (b₁ a))

cong-F : ∀ {A : Set}(B : A → Set){a₁ a₂ : A} →
         a₁ ≡ a₂ →
         B a₁ ↔ B a₂
cong-F B refl = ↔-refl
