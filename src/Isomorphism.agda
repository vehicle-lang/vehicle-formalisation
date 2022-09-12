{-# OPTIONS --postfix-projections #-}

module Isomorphism where

open import Level using (Level)
open import Data.Bool renaming (T to True)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (_⇔_; Equivalence) public
open import Function.Properties.Equivalence using (⇔-isEquivalence)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Relation.Nullary using (does; Dec; _because_; yes; no)

-- FIXME: move this
postulate
  fext : ∀ {ℓ₁ ℓ₂}{A : Set ℓ₁}{B : A → Set ℓ₂}{f g : (a : A) → B a} →
         ((a : A) → f a ≡ g a) → f ≡ g

open Equivalence

module _ {ℓ} where

  open IsEquivalence (⇔-isEquivalence {ℓ})
     renaming (refl to ⇔-refl;
               sym to ⇔-sym;
               trans to ⇔-trans)
     public

variable
  ℓ : Level

cong-∃ : ∀ {A : Set ℓ}{B₁ B₂ : A → Set ℓ} →
         ((a : A) → B₁ a ⇔ B₂ a) →
         (Σ A B₁) ⇔ Σ A B₂
cong-∃ eq .f (a , b₁) = a , eq a .f b₁
cong-∃ eq .g (a , b₂) = a , eq a .g b₂
cong-∃ eq .cong₁ refl = refl
cong-∃ eq .cong₂ refl = refl

known : ∀ {A : Set ℓ}{B : A → Set ℓ} a →
        B a ⇔ (Σ[ a' ∈ A ] (a' ≡ a × B a'))
known a .f b = a , refl , b
known a .g (a , refl , b) = b
known a .cong₁ refl = refl
known a .cong₂ refl = refl

or-left : ∀ {A : Set ℓ} → A ⇔ (A ⊎ ⊥)
or-left .f = inj₁
or-left .g (inj₁ x) = x
or-left .cong₁ refl = refl
or-left .cong₂ refl = refl

or-right : ∀ {A : Set ℓ} → A ⇔ (⊥ ⊎ A)
or-right .f = inj₂
or-right .g (inj₂ a) = a
or-right .cong₁ refl = refl
or-right .cong₂ refl = refl

⊤-fst : ∀ {A : Set ℓ} → A ⇔ (⊤ × A)
⊤-fst .f a = tt , a
⊤-fst .g (tt , a) = a
⊤-fst .cong₁ refl = refl
⊤-fst .cong₂ refl = refl

eq-cong : ∀ {A : Set ℓ} {a b c d : A} →
          a ≡ c →
          b ≡ d →
          (a ≡ b) ⇔ (c ≡ d)
eq-cong refl refl = ⇔-refl

⊥-fst : ∀ {A : Set} → ⊥ ⇔ (⊥ × A)
⊥-fst .f ()
⊥-fst .g ()

⊎-cong : ∀ {a b} {A C : Set a}{B D : Set b} → A ⇔ C → B ⇔ D → (A ⊎ B) ⇔ (C ⊎ D)
⊎-cong ac bd .f (inj₁ x) = inj₁ (ac .f x)
⊎-cong ac bd .f (inj₂ y) = inj₂ (bd .f y)
⊎-cong ac bd .g (inj₁ x) = inj₁ (ac .g x)
⊎-cong ac bd .g (inj₂ y) = inj₂ (bd .g y)
⊎-cong ac bd .cong₁ refl = refl
⊎-cong ac bd .cong₂ refl = refl

×-cong : ∀ {a b} {A C : Set a}{B D : Set b} → A ⇔ C → B ⇔ D → (A × B) ⇔ (C × D)
×-cong ac bd .f (a , b) = (ac .f a) , (bd .f b)
×-cong ac bd .g (c , d) = (ac .g c) , (bd .g d)
×-cong ac bd .cong₁ refl = refl
×-cong ac bd .cong₂ refl = refl

cong-True : ∀ {b₁ b₂ : Bool} → b₁ ≡ b₂ → True b₁ ⇔ True b₂
cong-True refl = ⇔-refl

True-∧ : ∀ {b₁ b₂ : Bool} → (True b₁ × True b₂) ⇔ True (b₁ ∧ b₂)
True-∧ {true} {true} .f (tt , tt) = tt
True-∧ {true} {true} .g x = tt , tt
True-∧ .cong₁ refl = refl
True-∧ .cong₂ refl = refl

True-∨ : ∀ {b₁ b₂ : Bool} → (True b₁ ⊎ True b₂) ⇔ True (b₁ ∨ b₂)
True-∨ {false} {b₂} .f (inj₂ y) = y
True-∨ {true}  {b₂} .f _ = tt
True-∨ {false} {b₂} .g = inj₂
True-∨ {true} {b₂} .g = inj₁
True-∨ .cong₁ refl = refl
True-∨ .cong₂ refl = refl

⊥-bool : ∀ {b} → b ≡ false → ⊥ ⇔ True b
⊥-bool refl .f ()
⊥-bool refl .g ()
⊥-bool refl .cong₁ refl = refl
⊥-bool refl .cong₂ refl = refl

⊤-bool : ∀ {b} → b ≡ true → ⊤ ⇔ True b
⊤-bool refl .f tt = tt
⊤-bool refl .g tt = tt
⊤-bool refl .cong₁ refl = refl
⊤-bool refl .cong₂ refl = refl

does-cong : ∀ {P : Set} (x : Dec P) → True (x .does) ⇔ P
does-cong (no p) .f ()
does-cong (no p) .g = p
does-cong (yes p) .f tt = p
does-cong (yes p) .g _ = tt
does-cong _ .cong₁ refl = refl
does-cong _ .cong₂ refl = refl

variable
  A B : Set
  P : A → Set
  Q : B → Set

and-comm-left : (A × Σ[ b ∈ B ] Q b) ⇔ (Σ[ b ∈ B ] (A × Q b))
and-comm-left .f (a , b , q) = b , a , q
and-comm-left .g (b , a , q) = a , b , q
and-comm-left .cong₁ refl = refl
and-comm-left .cong₂ refl = refl

and-comm-right : ((Σ[ a ∈ A ] P a) × B) ⇔ (Σ[ a ∈ A ] (P a × B))
and-comm-right .f ((a , p) , b) = a , p , b
and-comm-right .g (a , p , b) = (a , p) , b
and-comm-right .cong₁ refl = refl
and-comm-right .cong₂ refl = refl

or-comm-right : B → (A ⊎ Σ[ b ∈ B ] Q b) ⇔ (Σ[ b ∈ B ] (A ⊎ Q b))
or-comm-right b .f (inj₁ a) = b , inj₁ a
or-comm-right b .f (inj₂ (b' , q)) = b' , inj₂ q
or-comm-right b .g (b' , inj₁ a) = inj₁ a
or-comm-right b .g (b' , inj₂ q) = inj₂ (b' , q)
or-comm-right b .cong₁ refl = refl
or-comm-right b .cong₂ refl = refl

or-comm-left : A → ((Σ[ a ∈ A ] P a) ⊎ B) ⇔ (Σ[ a ∈ A ] (P a ⊎ B))
or-comm-left a₀ .f (inj₁ (a , p)) = a , inj₁ p
or-comm-left a₀ .f (inj₂ b)       = a₀ , inj₂ b
or-comm-left a₀ .g (a , inj₁ p) = inj₁ (a , p)
or-comm-left a₀ .g (a , inj₂ b) = inj₂ b
or-comm-left a₀ .cong₁ refl = refl
or-comm-left a₀ .cong₂ refl = refl
