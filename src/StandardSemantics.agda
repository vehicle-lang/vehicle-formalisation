{-# OPTIONS --postfix-projections #-} -- --safe #-}

module StandardSemantics where

open import Level using (Lift; lift; lower; 0ℓ; suc)
open import Data.Bool using (true; false; _∧_; _∨_; not)
                   renaming (Bool to 𝔹; if_then_else_ to ifᵇ_then_else_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; {- suc;-} _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; _≤ᵇ_) renaming (_+_ to _+ℚ_; _*_ to _*ℚ_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym; cong₂)

open import MiniVehicle
open import Interpretation

module _ (extFunc : ℚ → ℚ) where
  open Model

  ℳ : Model (suc 0ℓ) 0ℓ
  ℳ .⟦Type⟧ = Set
  ℳ ._==>_ X Y = X → Y
  ℳ .⟦id⟧ = λ x → x
  ℳ ._∘_ f g x = f (g x)
  ℳ ._⟦×⟧_ = _×_
  ℳ .⟦⊤⟧ = ⊤
  ℳ .⟦terminal⟧ x = tt
  ℳ .⟦proj₁⟧ = proj₁
  ℳ .⟦proj₂⟧ = proj₂
  ℳ .⟨_,_⟩ f g x = f x , g x
  ℳ ._⟦⇒⟧_ X Y = X → Y
  ℳ .⟦Λ⟧ f x y = f (x , y)
  ℳ .⟦eval⟧ (f , x) = f x
  ℳ .⟦∀⟧ A = ∀ n → A n
  ℳ .⟦∀-intro⟧ f x n = f n x
  ℳ .⟦∀-elim⟧ n f = f n
  ℳ .Mon X = X
  ℳ .⟦return⟧ x = x
  ℳ .⟦extend⟧ f = f
  ℳ .⟦Num⟧ _ = ℚ
  ℳ .⟦add⟧ (x , y) = x +ℚ y
  ℳ .⟦mul⟧ (x , y) = x *ℚ y
  ℳ .⟦num⟧ q _ = q
  ℳ .⟦const⟧ q = q
  ℳ .⟦extFunc⟧ = extFunc
  ℳ .⟦Bool⟧ _ = 𝔹
  ℳ .⟦not⟧ = not
  ℳ .⟦and⟧ (x , y) = x ∧ y
  ℳ .⟦or⟧ (x , y) = x ∨ y
  ℳ .⟦≤⟧ (q₁ , q₂) = q₁ ≤ᵇ q₂
  ℳ .⟦if⟧ ((tr , fa) , false) = fa
  ℳ .⟦if⟧ ((tr , fa) , true) = tr
  ℳ .⟦Index⟧ = Fin

  module ℐ = Interpret ℳ

-- open import TypeSemantics
--               Set
--               (λ x → 𝔹)
--               (λ x → ℚ)
--               (λ X → X)
--               (λ A B → A → B)
--               (Fin)
--               (λ A → (n : ℕ) → A n)
--               (⊤)
--               (_×_)
--   public

-- {-
-- -- FIXME: this needs to be a setoid??? Ought the denotations be
-- -- setoids too?
-- ⟦_⟧kind : Kind → Set₁
-- ⟦ Nat ⟧kind  = Lift _ ℕ
-- ⟦ Type ⟧kind = Set

-- -- ⟦_⟧kind-Eq : (κ : Kind) → ⟦ κ ⟧kind → ⟦ κ ⟧kind → Set
-- -- ⟦ Nat ⟧kind-Eq  x y = x .lower ≡ y .lower
-- -- ⟦ Type ⟧kind-Eq x y = x ↔ y

-- ⟦_⟧kctxt : KindContext → Set
-- ⟦ ε ⟧kctxt      = ⊤
-- ⟦ K ,-ℕ ⟧kctxt = ⟦ K ⟧kctxt × ℕ

-- ⟦_⟧tyvar : ∀ {K} → K ⊢Tv → ⟦ K ⟧kctxt → ⟦ Nat ⟧kind
-- ⟦ zero ⟧tyvar   (_ , n) = lift n
-- ⟦ succ x ⟧tyvar (δ , _) = ⟦ x ⟧tyvar δ

-- ⟦_⟧ty : ∀ {K κ} → K ⊢T κ → ⟦ K ⟧kctxt → ⟦ κ ⟧kind
-- ⟦ var x ⟧ty           δ = ⟦ x ⟧tyvar δ
-- ⟦ Bool constraint ⟧ty δ = 𝔹
-- ⟦ Num x ⟧ty           δ = ℚ
-- ⟦ A ⇒ B ⟧ty          δ = ⟦ A ⟧ty δ → ⟦ B ⟧ty δ
-- ⟦ Index n ⟧ty         δ = Fin (⟦ n ⟧ty δ .lower)
-- ⟦ Array n A ⟧ty       δ = Fin (⟦ n ⟧ty δ .lower) → ⟦ A ⟧ty δ
-- ⟦ Forall A ⟧ty        δ = (n : ℕ) → ⟦ A ⟧ty (δ , n)

-- ⟦_⟧ren : ∀ {K K'} (ρ : K' ⇒ᵣ K) → ⟦ K' ⟧kctxt → ⟦ K ⟧kctxt
-- ⟦_⟧ren {ε} ρ ks = tt
-- ⟦_⟧ren {K ,-ℕ} ρ ks = ⟦_⟧ren {K} (λ x → ρ (succ x)) ks , (⟦ ρ zero ⟧tyvar ks .lower)

-- ⟦_⟧subst : ∀ {K K'} → (σ : K ⊢Tv → K' ⊢T Nat) → ⟦ K' ⟧kctxt → ⟦ K ⟧kctxt
-- ⟦_⟧subst {ε} σ ks = tt
-- ⟦_⟧subst {K ,-ℕ} σ ks = ⟦ (λ x → σ (succ x)) ⟧subst ks , (⟦ σ zero ⟧ty ks .lower)

-- ⟦_succ⟧ren : ∀ {K K'} (ρ : K' ⇒ᵣ K) → ∀ {ks n} → ⟦ (λ x → succ (ρ x)) ⟧ren (ks , n) ≡ ⟦ ρ ⟧ren ks
-- ⟦_succ⟧ren {ε} ρ = refl
-- ⟦_succ⟧ren {K ,-ℕ} ρ {ks}{n} rewrite ⟦ (λ x → ρ (succ x)) succ⟧ren {ks}{n} = refl

-- ren-⟦tyvar⟧ : ∀ {K K'} (ρ : K' ⇒ᵣ K) (x : K ⊢Tv) →
--              ∀ {ks} → ⟦ ρ x ⟧tyvar ks ≡ ⟦ x ⟧tyvar (⟦ ρ ⟧ren ks)
-- ren-⟦tyvar⟧ ρ zero     = cong lift refl
-- ren-⟦tyvar⟧ ρ (succ x) = ren-⟦tyvar⟧ (λ x → ρ (succ x)) x

-- subst-⟦tyvar⟧ : ∀ {K K'} (σ : K ⊢Tv → K' ⊢T Nat) (x : K ⊢Tv) →
--                ∀ {ks} → ⟦ σ x ⟧ty ks ≡ ⟦ x ⟧tyvar (⟦ σ ⟧subst ks)
-- subst-⟦tyvar⟧ σ zero     = refl
-- subst-⟦tyvar⟧ σ (succ x) = subst-⟦tyvar⟧ (λ x → σ (succ x)) x

-- ren-∘ : ∀ {K₁ K₂ K₃} (ρ₁ : K₁ ⇒ᵣ K₂)(ρ₂ : K₂ ⇒ᵣ K₃) →
--        ∀ ks → ⟦ (λ x → ρ₁ (ρ₂ x)) ⟧ren ks ≡ ⟦ ρ₂ ⟧ren (⟦ ρ₁ ⟧ren ks)
-- ren-∘ {K₁} {K₂} {ε} ρ₁ ρ₂ ks = refl
-- ren-∘ {K₁} {K₂} {K₃ ,-ℕ} ρ₁ ρ₂ ks =
--   trans (cong (λ □ → □ , ⟦ ρ₁ (ρ₂ zero) ⟧tyvar ks .lower)
--               (ren-∘ ρ₁ (λ x → ρ₂ (succ x)) ks))
--         (cong (λ □ → ⟦ (λ x → ρ₂ (succ x)) ⟧ren (⟦ ρ₁ ⟧ren ks) , □)
--               (cong lower (ren-⟦tyvar⟧ ρ₁ (ρ₂ zero))))

-- ⟦id⟧ren : ∀ {K}{ks : ⟦ K ⟧kctxt} → ⟦ (λ x → x) ⟧ren ks ≡ ks
-- ⟦id⟧ren {ε} {ks} = refl
-- ⟦id⟧ren {K ,-ℕ} {ks , n} = cong (λ □ → □ , n) (trans (⟦ (λ x → x) succ⟧ren {ks}) ⟦id⟧ren)

-- ⟦wk⟧-eq : ∀ {K}{ks : ⟦ K ,-ℕ ⟧kctxt} → ⟦ wk ⟧ren ks ≡ ks .proj₁
-- ⟦wk⟧-eq {K}{ks , n} = trans (⟦ (λ x → x) succ⟧ren {ks}) ⟦id⟧ren

-- cong-Λ : ∀ {A : Set}{B₁ B₂ : A → Set} →
--            ((a : A) → B₁ a ≡ B₂ a) →
--            ((a : A) → B₁ a) ≡ ((a : A) → B₂ a)
-- cong-Λ {A} eq = cong (λ □ → (a : A) → □ a) (fext eq)

-- ren-⟦Type⟧ : ∀ {K K'} (ρ : K' ⇒ᵣ K) {κ} (A : K ⊢T κ) →
--              ∀ {ks} → ⟦ ren-Type ρ A ⟧ty ks ≡ ⟦ A ⟧ty (⟦ ρ ⟧ren ks)
-- ren-⟦Type⟧ ρ (var x) = ren-⟦tyvar⟧ ρ x
-- ren-⟦Type⟧ ρ (Bool constraint) = refl
-- ren-⟦Type⟧ ρ (Num x) = refl
-- ren-⟦Type⟧ ρ (A ⇒ B) {ks} rewrite ren-⟦Type⟧ ρ A {ks} rewrite ren-⟦Type⟧ ρ B {ks} = refl
-- ren-⟦Type⟧ ρ (Index N) {ks} rewrite ren-⟦Type⟧ ρ N {ks} = refl
-- ren-⟦Type⟧ ρ (Array N A) {ks} rewrite ren-⟦Type⟧ ρ N {ks} rewrite ren-⟦Type⟧ ρ A {ks} = refl
-- ren-⟦Type⟧ ρ (Forall A) {ks} =
--   cong-Λ (λ n → trans (ren-⟦Type⟧ (under ρ) A) (cong (λ □ → ⟦ A ⟧ty (□ , n)) ⟦ ρ succ⟧ren))

-- ren-subst : ∀ {K K'}{ks : ⟦ K' ⟧kctxt} → (ρ : K' ⇒ᵣ K) → ⟦ (λ x → var (ρ x)) ⟧subst ks ≡ ⟦ ρ ⟧ren ks
-- ren-subst {ε} {K'} {ks} ρ = refl
-- ren-subst {K ,-ℕ} {K'} {ks} ρ = cong (λ □ → □ , ⟦ ρ zero ⟧tyvar ks .lower) (ren-subst (λ x → ρ (succ x)))

-- ⟦id⟧-subst : ∀ {K}{ks : ⟦ K ⟧kctxt} → ⟦ var ⟧subst ks ≡ ks
-- ⟦id⟧-subst = trans (ren-subst (λ x → x)) ⟦id⟧ren

-- subst-ren : ∀ {K₁ K₂ K₃} →
--             (ρ : K₁ ⇒ᵣ K₂)
--             (σ : K₃ ⊢Tv → K₂ ⊢T Nat) →
--             ∀ {ks} → ⟦ (λ x → ren-Type ρ (σ x)) ⟧subst ks ≡ ⟦ σ ⟧subst (⟦ ρ ⟧ren ks)
-- subst-ren {K₁} {K₂} {ε} ρ σ = refl
-- subst-ren {K₁} {K₂} {K₃ ,-ℕ} ρ σ =
--   cong₂ _,_ (subst-ren ρ (λ x → σ (succ x))) (cong lower (ren-⟦Type⟧ ρ (σ zero)))

-- subst-⟦Type⟧ : ∀ {K K'} (σ : K ⊢Tv → K' ⊢T Nat) {κ} (A : K ⊢T κ) →
--               ∀ {ks} → ⟦ subst-Type σ A ⟧ty ks ≡ ⟦ A ⟧ty (⟦ σ ⟧subst ks)
-- subst-⟦Type⟧ σ (var x) = subst-⟦tyvar⟧ σ x
-- subst-⟦Type⟧ σ (Bool constraint) = refl
-- subst-⟦Type⟧ σ (Num x) = refl
-- subst-⟦Type⟧ σ (A ⇒ B) = cong₂ (λ X Y → X → Y) (subst-⟦Type⟧ σ A) (subst-⟦Type⟧ σ B)
-- subst-⟦Type⟧ σ (Index N) = cong Fin (cong lower (subst-⟦Type⟧ σ N))
-- subst-⟦Type⟧ σ (Array N A) =
--   cong₂ (λ n X → Fin n → X) (cong lower (subst-⟦Type⟧ σ N)) (subst-⟦Type⟧ σ A)
-- subst-⟦Type⟧ σ (Forall A) =
--   cong-Λ λ n →
--     trans (subst-⟦Type⟧ (binder σ) A)
--           (cong (λ □ → ⟦ A ⟧ty (□ , n))
--                 (trans (subst-ren wk σ) (cong ⟦ σ ⟧subst ⟦wk⟧-eq)))

-- ⟦_⟧ctxt : ∀ {K} → Context K → ⟦ K ⟧kctxt → Set
-- ⟦ ε ⟧ctxt      δ = ⊤
-- ⟦ Γ ,- A ⟧ctxt δ = ⟦ Γ ⟧ctxt δ × ⟦ A ⟧ty δ

-- ren-⟦Context⟧ : ∀ {K K'} (ρ : K' ⇒ᵣ K) (Γ : Context K) →
--                 ∀ {ks} → ⟦ ren-Context ρ Γ ⟧ctxt ks ≡ ⟦ Γ ⟧ctxt (⟦ ρ ⟧ren ks)
-- ren-⟦Context⟧ ρ ε = refl
-- ren-⟦Context⟧ ρ (Γ ,- A) {ks} = trans (cong (λ □ → □ × ⟦ ren-Type ρ A ⟧ty ks) (ren-⟦Context⟧ ρ Γ))
--                                       (cong (λ □ → ⟦ Γ ⟧ctxt (⟦ ρ ⟧ren ks) × □) (ren-⟦Type⟧ ρ A))

-- -}

-- ⟦_⟧var : ∀ {K Γ A} → K ⊢ Γ ∋ A → ∀ δ → ⟦ Γ ⟧ctxt δ → ⟦ A ⟧ty δ
-- ⟦ zero ⟧var   δ (_ , a) = a
-- ⟦ succ x ⟧var δ (γ , _) = ⟦ x ⟧var δ γ

-- module TermSem (f : ℚ → ℚ) where

--   ⟦_⟧tm : ∀ {K Γ A} → K / Γ ⊢ A → ∀ δ → ⟦ Γ ⟧ctxt δ → ⟦ A ⟧ty δ
--   ⟦ var x ⟧tm δ γ = ⟦ x ⟧var δ γ
--   ⟦ ƛ t ⟧tm δ γ = λ a → ⟦ t ⟧tm δ (γ , a)
--   ⟦ s ∙ t ⟧tm δ γ = ⟦ s ⟧tm δ γ (⟦ t ⟧tm δ γ)
--   ⟦_⟧tm {Γ = Γ} (Λ t) δ γ n = ⟦ t ⟧tm (δ , n) (coerce (sym eq) γ)
--     where eq : ⟦ ren-Context wk Γ ⟧ctxt (δ , n) ≡ ⟦ Γ ⟧ctxt δ
--           eq = trans (ren-⟦Context⟧ wk Γ) (cong (⟦ Γ ⟧ctxt) ⟦wk⟧-eq)
--   ⟦ _•_ {A = A} t N ⟧tm ks γ =
--     coerce (trans (cong (λ □ → ⟦ A ⟧ty (□ , ⟦ N ⟧ty ks .lower)) (sym ⟦id⟧-subst))
--                   (sym (subst-⟦Type⟧ (single-sub N) A)))
--            (⟦ t ⟧tm ks γ (⟦ N ⟧ty ks .lower))

--   ⟦ func t ⟧tm δ γ = f (⟦ t ⟧tm δ γ)
--   ⟦ const x ⟧tm δ γ = x
--   ⟦ lift t ⟧tm δ γ = ⟦ t ⟧tm δ γ
--   ⟦ s `+ t ⟧tm δ γ = (⟦ s ⟧tm δ γ) +ℚ (⟦ t ⟧tm δ γ)
--   ⟦ s `* t ⟧tm δ γ = (⟦ s ⟧tm δ γ) *ℚ (⟦ t ⟧tm δ γ)

--   ⟦ array n A t ⟧tm δ γ = λ idx → ⟦ t ⟧tm δ (γ , idx)
--   ⟦ index n A s t ⟧tm δ γ = ⟦ s ⟧tm δ γ (⟦ t ⟧tm δ γ)

--   ⟦ s `≤ t ⟧tm δ γ  = (⟦ s ⟧tm δ γ) ≤ᵇ (⟦ t ⟧tm δ γ)
--   ⟦ if s then t else u ⟧tm δ γ = ifᵇ (⟦ s ⟧tm δ γ) then (⟦ t ⟧tm δ γ) else (⟦ u ⟧tm δ γ)
--   ⟦ `¬ t ⟧tm δ γ = not (⟦ t ⟧tm δ γ)
--   ⟦ s `∧ t ⟧tm δ γ = (⟦ s ⟧tm δ γ) ∧ (⟦ t ⟧tm δ γ)
--   ⟦ s `∨ t ⟧tm δ γ = (⟦ s ⟧tm δ γ) ∨ (⟦ t ⟧tm δ γ)
