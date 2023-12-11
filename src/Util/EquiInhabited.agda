{-# OPTIONS --safe #-}

module Util.EquiInhabited where

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
cong-∃ eq .to        (a , b₁) = a , eq a .to b₁
cong-∃ eq .from      (a , b₂) = a , eq a .from b₂
cong-∃ eq .to-cong   refl     = refl
cong-∃ eq .from-cong refl     = refl

known : ∀ {A : Set ℓ}{B : A → Set ℓ} a →
        B a ⇔ (Σ[ a' ∈ A ] (a' ≡ a × B a'))
known a .to        b = a , refl , b
known a .from     (a , refl , b) = b
known a .to-cong   refl = refl
known a .from-cong refl = refl

or-left : ∀ {A : Set ℓ} → A ⇔ (A ⊎ ⊥)
or-left .to = inj₁
or-left .from (inj₁ x) = x
or-left .to-cong refl = refl
or-left .from-cong refl = refl

or-right : ∀ {A : Set ℓ} → A ⇔ (⊥ ⊎ A)
or-right .to = inj₂
or-right .from (inj₂ a) = a
or-right .to-cong refl = refl
or-right .from-cong refl = refl

⊤-fst : ∀ {A : Set ℓ} → A ⇔ (⊤ × A)
⊤-fst .to a = tt , a
⊤-fst .from (tt , a) = a
⊤-fst .to-cong refl = refl
⊤-fst .from-cong refl = refl

eq-cong : ∀ {A : Set ℓ} {a b c d : A} →
          a ≡ c →
          b ≡ d →
          (a ≡ b) ⇔ (c ≡ d)
eq-cong refl refl = ⇔-refl

⊥-fst : ∀ {A : Set} → ⊥ ⇔ (⊥ × A)
⊥-fst .to ()
⊥-fst .from ()

-- stdlib v2.0
⊎-cong : ∀ {a b} {A C : Set a}{B D : Set b} → A ⇔ C → B ⇔ D → (A ⊎ B) ⇔ (C ⊎ D)
⊎-cong ac bd .to (inj₁ x) = inj₁ (ac .to x)
⊎-cong ac bd .to (inj₂ y) = inj₂ (bd .to y)
⊎-cong ac bd .from (inj₁ x) = inj₁ (ac .from x)
⊎-cong ac bd .from (inj₂ y) = inj₂ (bd .from y)
⊎-cong ac bd .to-cong refl = refl
⊎-cong ac bd .from-cong refl = refl

-- stdlib v2.0
×-cong : ∀ {a b} {A C : Set a}{B D : Set b} → A ⇔ C → B ⇔ D → (A × B) ⇔ (C × D)
×-cong ac bd .to (a , b) = (ac .to a) , (bd .to b)
×-cong ac bd .from (c , d) = (ac .from c) , (bd .from d)
×-cong ac bd .to-cong refl = refl
×-cong ac bd .from-cong refl = refl

×-congˡ : ∀ {a b} {A C : Set a} {B : Set b} → A ⇔ C → (A × B) ⇔ (C × B)
×-congˡ A⇔C = ×-cong A⇔C ⇔-refl

cong-True : ∀ {b₁ b₂ : Bool} → b₁ ≡ b₂ → True b₁ ⇔ True b₂
cong-True refl = ⇔-refl

⊥-bool : ∀ {b} → b ≡ false → ⊥ ⇔ True b
⊥-bool refl .to ()
⊥-bool refl .from ()
⊥-bool refl .to-cong refl = refl
⊥-bool refl .from-cong refl = refl

⊤-bool : ∀ {b} → b ≡ true → ⊤ ⇔ True b
⊤-bool refl .to tt = tt
⊤-bool refl .from tt = tt
⊤-bool refl .to-cong refl = refl
⊤-bool refl .from-cong refl = refl

does-cong : ∀ {P : Set} (x : Dec P) → True (x .does) ⇔ P
does-cong (no p) .to ()
does-cong (no p) .from = p
does-cong (yes p) .to tt = p
does-cong (yes p) .from _ = tt
does-cong _ .to-cong refl = refl
does-cong _ .from-cong refl = refl

variable
  A B : Set
  P : A → Set
  Q : B → Set

and-comm-left : (A × Σ[ b ∈ B ] Q b) ⇔ (Σ[ b ∈ B ] (A × Q b))
and-comm-left .to (a , b , q) = b , a , q
and-comm-left .from (b , a , q) = a , b , q
and-comm-left .to-cong refl = refl
and-comm-left .from-cong refl = refl

and-comm-right : ((Σ[ a ∈ A ] P a) × B) ⇔ (Σ[ a ∈ A ] (P a × B))
and-comm-right .to ((a , p) , b) = a , p , b
and-comm-right .from (a , p , b) = (a , p) , b
and-comm-right .to-cong refl = refl
and-comm-right .from-cong refl = refl

or-comm-right : B → (A ⊎ Σ[ b ∈ B ] Q b) ⇔ (Σ[ b ∈ B ] (A ⊎ Q b))
or-comm-right b .to (inj₁ a) = b , inj₁ a
or-comm-right b .to (inj₂ (b' , q)) = b' , inj₂ q
or-comm-right b .from (b' , inj₁ a) = inj₁ a
or-comm-right b .from (b' , inj₂ q) = inj₂ (b' , q)
or-comm-right b .to-cong refl = refl
or-comm-right b .from-cong refl = refl

or-comm-left : A → ((Σ[ a ∈ A ] P a) ⊎ B) ⇔ (Σ[ a ∈ A ] (P a ⊎ B))
or-comm-left a₀ .to (inj₁ (a , p)) = a , inj₁ p
or-comm-left a₀ .to (inj₂ b)       = a₀ , inj₂ b
or-comm-left a₀ .from (a , inj₁ p) = inj₁ (a , p)
or-comm-left a₀ .from (a , inj₂ b) = inj₂ b
or-comm-left a₀ .to-cong refl = refl
or-comm-left a₀ .from-cong refl = refl

Σ-distribˡ-⊎ : (Σ A (λ a → P a ⊎ Q a)) ⇔ (Σ A P ⊎ Σ A Q)
Σ-distribˡ-⊎ .to (a , inj₁ p) = inj₁ (a , p)
Σ-distribˡ-⊎ .to (a , inj₂ q) = inj₂ (a , q)
Σ-distribˡ-⊎ .from (inj₁ (a , p)) = a , inj₁ p
Σ-distribˡ-⊎ .from (inj₂ (a , q)) = a , inj₂ q
Σ-distribˡ-⊎ .to-cong refl = refl
Σ-distribˡ-⊎ .from-cong refl = refl

