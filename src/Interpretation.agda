{-# OPTIONS --postfix-projections #-}

module Interpretation where

open import Level using (suc; 0ℓ; _⊔_; Lift; lift; lower)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Rational using (ℚ)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality
            using (_≡_; refl; cong; trans; cong₂; sym)

open import Isomorphism using (fext)

-- FIXME: move to Util
cong₃ : ∀ {a b c d} {A : Set a}{B : Set b}{C : Set c}{D : Set d} (f : A → B → C → D) {x y u v t w} → x ≡ y → u ≡ v → t ≡ w → f x u t ≡ f y v w
cong₃ f refl refl refl = refl

open import MiniVehicle.Qualifiers

record Model ℓ m : Set (suc ℓ ⊔ suc m) where
  field
    ⟦Type⟧ : Set ℓ
    _==>_ : ⟦Type⟧ → ⟦Type⟧ → Set m

    ⟦id⟧  : ∀ {X} → X ==> X
    _∘_   : ∀ {X Y Z} → Y ==> Z → X ==> Y → X ==> Z

    -- Sets as types
    Flat : Set → ⟦Type⟧
    elem : ∀ {A X} → A → X ==> Flat A

    -- finite products
    _⟦×⟧_      : ⟦Type⟧ → ⟦Type⟧ → ⟦Type⟧
    ⟦⊤⟧        : ⟦Type⟧
    ⟦terminal⟧ : ∀ {X} → X ==> ⟦⊤⟧
    ⟦proj₁⟧    : ∀ {X Y} → (X ⟦×⟧ Y) ==> X
    ⟦proj₂⟧    : ∀ {X Y} → (X ⟦×⟧ Y) ==> Y
    ⟨_,_⟩      : ∀ {X Y Z} → (X ==> Y) → (X ==> Z) → (X ==> (Y ⟦×⟧ Z))

    -- closure
    _⟦⇒⟧_ : ⟦Type⟧ → ⟦Type⟧ → ⟦Type⟧
    ⟦Λ⟧    : ∀ {X Y Z} → ((X ⟦×⟧ Y) ==> Z) → (X ==> (Y ⟦⇒⟧ Z))
    ⟦eval⟧ : ∀ {X Y} → ((X ⟦⇒⟧ Y) ⟦×⟧ X) ==> Y

    -- Universal types
    ⟦∀⟧       : ∀ {I : Set} → (I → ⟦Type⟧) → ⟦Type⟧
    ⟦∀-intro⟧ : ∀ {I X A} → (∀ (n : I) → X ==> A n) → X ==> ⟦∀⟧ A
    ⟦∀-elim⟧  : ∀ {I A} (n : I) → ⟦∀⟧ A ==> A n

    -- Monad
    Mon      : ⟦Type⟧ → ⟦Type⟧
    ⟦return⟧ : ∀ {X} → X ==> Mon X
    ⟦extend⟧ : ∀ {X Y Z} → ((X ⟦×⟧ Y) ==> Mon Z) → (X ⟦×⟧ Mon Y) ==> Mon Z

    -- Actual stuff
    ⟦Bool⟧ : LinearityVal → PolarityVal → ⟦Type⟧
    ⟦Num⟧  : LinearityVal → ⟦Type⟧

    ⟦not⟧ : ∀ {l p₁ p₂} → (Flat (NegPolRel p₁ p₂) ⟦×⟧ ⟦Bool⟧ l p₁) ==> ⟦Bool⟧ l p₂
    ⟦and⟧ ⟦or⟧ : ∀ {l₁ l₂ l₃ p₁ p₂ p₃} →
                (Flat (MaxLinRel l₁ l₂ l₃) ⟦×⟧
                 (Flat (MaxPolRel p₁ p₂ p₃) ⟦×⟧
                  (⟦Bool⟧ l₁ p₁ ⟦×⟧ ⟦Bool⟧ l₂ p₂))) ==> ⟦Bool⟧ l₃ p₃

    ⟦if⟧ : ∀ {X} → ((Mon X ⟦×⟧ Mon X) ⟦×⟧ ⟦Bool⟧ linear U) ==> Mon X

    ⟦∃⟧    : ∀ {p₁ p₂ l} →
            (Flat (QuantifyRel p₁ p₂) ⟦×⟧ (⟦Num⟧ linear ⟦⇒⟧ Mon (⟦Bool⟧ l p₁))) ==> ⟦Bool⟧ l p₂

    ⟦add⟧     : ∀ {l₁ l₂ l₃} → (Flat (MaxLinRel l₁ l₂ l₃) ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Num⟧ l₃
    ⟦mul⟧     : ∀ {l₁ l₂ l₃} → (Flat (MulRel l₁ l₂ l₃) ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Num⟧ l₃
    ⟦const⟧   : ∀ {X} → ℚ → X ==> ⟦Num⟧ const
    ⟦extFunc⟧ : ⟦Num⟧ linear ==> Mon (⟦Num⟧ linear)
    ⟦≤⟧       : ∀ {l₁ l₂ l₃} → (Flat (MaxLinRel l₁ l₂ l₃) ⟦×⟧ (⟦Num⟧ l₁ ⟦×⟧ ⟦Num⟧ l₂)) ==> ⟦Bool⟧ l₃ U

    -- Indexes and Arrays
    ⟦Index⟧ : ℕ → ⟦Type⟧
    ⟦idx⟧   : (n : ℕ)(i : Fin n) → ∀ {X} → X ==> ⟦Index⟧ n

module Interpret {ℓ}{m} (ℳ : Model ℓ m) where

  open import MiniVehicle
  open Model ℳ

  ⟦_⟧kind : Kind → Set ℓ
  ⟦ Nat ⟧kind = Lift _ ℕ
  ⟦ Linearity ⟧kind = Lift _ LinearityVal
  ⟦ Polarity ⟧kind = Lift _ PolarityVal
  ⟦ Type ⟧kind = ⟦Type⟧

  ⟦_⟧kctxt : KindContext → Set ℓ
  ⟦ ε ⟧kctxt      = Lift _ ⊤
  ⟦ K ,- κ ⟧kctxt = ⟦ K ⟧kctxt × ⟦ κ ⟧kind

  ⟦_⟧tyvar : ∀ {K κ} → K ⊢Tv κ → ⟦ K ⟧kctxt → ⟦ κ ⟧kind
  ⟦ zero ⟧tyvar   (_  , n) = n
  ⟦ succ x ⟧tyvar (ks , _) = ⟦ x ⟧tyvar ks

  ⟦_⟧ren : ∀ {K K'} (ρ : K' ⇒ᵣ K) → ⟦ K' ⟧kctxt → ⟦ K ⟧kctxt
  ⟦_⟧ren {ε} ρ ks = lift tt
  ⟦_⟧ren {K ,- κ} ρ ks = ⟦_⟧ren {K} (λ x → ρ (succ x)) ks , ⟦ ρ zero ⟧tyvar ks


  ⟦_⟧ty : ∀ {K κ} → K ⊢T κ → ⟦ K ⟧kctxt → ⟦ κ ⟧kind
  ⟦ var x ⟧ty ks = ⟦ x ⟧tyvar ks
  ⟦ Bool l x ⟧ty ks = ⟦Bool⟧ (⟦ l ⟧ty ks .lower) (⟦ x ⟧ty ks .lower)
  ⟦ Num x ⟧ty ks = ⟦Num⟧ (⟦ x ⟧ty ks .lower)
  ⟦ A ⇒ B ⟧ty ks = (⟦ A ⟧ty ks) ⟦⇒⟧ Mon (⟦ B ⟧ty ks)
  ⟦ Index N ⟧ty ks = ⟦Index⟧ (⟦ N ⟧ty ks .lower)
  ⟦ Vec N A ⟧ty ks = (⟦Index⟧ (⟦ N ⟧ty ks .lower)) ⟦⇒⟧ Mon (⟦ A ⟧ty ks)
  ⟦ Forall Nat A ⟧ty ks = ⟦∀⟧ (λ n → Mon (⟦ A ⟧ty (ks , lift n)))
  ⟦ Forall Linearity A ⟧ty ks = ⟦∀⟧ (λ l → Mon (⟦ A ⟧ty (ks , lift l)))
  ⟦ Forall Polarity A ⟧ty ks = ⟦∀⟧ (λ p → Mon (⟦ A ⟧ty (ks , lift p)))
  ⟦ [ n ] ⟧ty ks = lift n
  ⟦ LinearityConst l ⟧ty ks = lift l
  ⟦ PolarityConst p ⟧ty ks = lift p
  ⟦ MaxLin l₁ l₂ l₃ ⟧ty ks =
    Flat (MaxLinRel (⟦ l₁ ⟧ty ks .lower) (⟦ l₂ ⟧ty ks .lower) (⟦ l₃ ⟧ty ks .lower))
  ⟦ HasMul l₁ l₂ l₃ ⟧ty ks =
    Flat (MulRel (⟦ l₁ ⟧ty ks .lower) (⟦ l₂ ⟧ty ks .lower) (⟦ l₃ ⟧ty ks .lower))
  ⟦ MaxPol p₁ p₂ p₃ ⟧ty ks =
    Flat (MaxPolRel (⟦ p₁ ⟧ty ks .lower) (⟦ p₂ ⟧ty ks .lower) (⟦ p₃ ⟧ty ks .lower))
  ⟦ NegPol p₁ p₂ ⟧ty ks =
    Flat (NegPolRel (⟦ p₁ ⟧ty ks .lower) (⟦ p₂ ⟧ty ks .lower))
  ⟦ Quantify p₁ p₂ ⟧ty ks =
    Flat (QuantifyRel (⟦ p₁ ⟧ty ks .lower) (⟦ p₂ ⟧ty ks .lower))

  ⟦_⟧subst : ∀ {K K'} → (K' ⇒ₛ K) → ⟦ K' ⟧kctxt → ⟦ K ⟧kctxt
  ⟦_⟧subst {ε} σ ks = lift tt
  ⟦_⟧subst {K ,- κ} σ ks = ⟦ (λ x → σ (succ x)) ⟧subst ks , ⟦ σ zero ⟧ty ks

  ⟦_succ⟧ren : ∀ {K K'} (ρ : K' ⇒ᵣ K) →
              ∀ {ks κ v} →
              ⟦ (λ x → succ {κ' = κ} (ρ x)) ⟧ren (ks , v) ≡ ⟦ ρ ⟧ren ks
  ⟦_succ⟧ren {ε} ρ = refl
  ⟦_succ⟧ren {K ,- κ} ρ {ks} =
    cong (λ □ → (□ , ⟦ ρ zero ⟧tyvar ks)) ⟦ (λ x → ρ (succ x)) succ⟧ren

  ren-⟦tyvar⟧ : ∀ {K K'} (ρ : K' ⇒ᵣ K) {κ} (x : K ⊢Tv κ) →
               ∀ {ks} → ⟦ ρ x ⟧tyvar ks ≡ ⟦ x ⟧tyvar (⟦ ρ ⟧ren ks)
  ren-⟦tyvar⟧ ρ zero     = refl
  ren-⟦tyvar⟧ ρ (succ x) = ren-⟦tyvar⟧ (λ x → ρ (succ x)) x

  subst-⟦tyvar⟧ : ∀ {K K'} (σ : K' ⇒ₛ K) {κ} (x : K ⊢Tv κ) →
                 ∀ {ks} → ⟦ σ x ⟧ty ks ≡ ⟦ x ⟧tyvar (⟦ σ ⟧subst ks)
  subst-⟦tyvar⟧ σ zero     = refl
  subst-⟦tyvar⟧ σ (succ x) = subst-⟦tyvar⟧ (λ x → σ (succ x)) x

  ren-∘ : ∀ {K₁ K₂ K₃} (ρ₁ : K₁ ⇒ᵣ K₂)(ρ₂ : K₂ ⇒ᵣ K₃) →
         ∀ ks → ⟦ (λ x → ρ₁ (ρ₂ x)) ⟧ren ks ≡ ⟦ ρ₂ ⟧ren (⟦ ρ₁ ⟧ren ks)
  ren-∘ {K₁} {K₂} {ε} ρ₁ ρ₂ ks = refl
  ren-∘ {K₁} {K₂} {K₃ ,- κ} ρ₁ ρ₂ ks =
    trans (cong (λ □ → □ , ⟦ ρ₁ (ρ₂ zero) ⟧tyvar ks)
                (ren-∘ ρ₁ (λ x → ρ₂ (succ x)) ks))
          (cong (λ □ → ⟦ (λ x → ρ₂ (succ x)) ⟧ren (⟦ ρ₁ ⟧ren ks) , □)
                (ren-⟦tyvar⟧ ρ₁ (ρ₂ zero)))

  ⟦id⟧ren : ∀ {K}{ks : ⟦ K ⟧kctxt} → ⟦ (λ x → x) ⟧ren ks ≡ ks
  ⟦id⟧ren {ε} {ks} = refl
  ⟦id⟧ren {K ,- κ} {ks , n} = cong (λ □ → □ , n) (trans (⟦ (λ x → x) succ⟧ren {ks}) ⟦id⟧ren)

  ⟦wk⟧-eq : ∀ {K κ}{ks : ⟦ K ,- κ ⟧kctxt} → ⟦ wk ⟧ren ks ≡ ks .proj₁
  ⟦wk⟧-eq {K}{κ}{ks , n} = trans (⟦ (λ x → x) succ⟧ren {ks}{κ}) ⟦id⟧ren

  ren-⟦Type⟧ : ∀ {K K'} (ρ : K' ⇒ᵣ K) {κ} (A : K ⊢T κ) →
             ∀ {ks} → ⟦ ren-Type ρ A ⟧ty ks ≡ ⟦ A ⟧ty (⟦ ρ ⟧ren ks)
  ren-⟦Type⟧ ρ (var x) = ren-⟦tyvar⟧ ρ x
  ren-⟦Type⟧ ρ (Bool l x) = cong₂ ⟦Bool⟧ (cong lower (ren-⟦Type⟧ ρ l)) (cong lower (ren-⟦Type⟧ ρ x))
  ren-⟦Type⟧ ρ (Num x) = cong ⟦Num⟧ (cong lower (ren-⟦Type⟧ ρ x))
  ren-⟦Type⟧ ρ (A ⇒ B) =
    cong₂ (λ □₁ □₂ → □₁ ⟦⇒⟧ (Mon □₂)) (ren-⟦Type⟧ ρ A) (ren-⟦Type⟧ ρ B)
  ren-⟦Type⟧ ρ (Index N) =
    cong (λ □ → ⟦Index⟧ (□ .lower)) (ren-⟦Type⟧ ρ N)
  ren-⟦Type⟧ ρ (Vec N A) =
    cong₂ (λ □₁ □₂ → ⟦Index⟧ (□₁ .lower) ⟦⇒⟧ (Mon □₂)) (ren-⟦Type⟧ ρ N) (ren-⟦Type⟧ ρ A)
  ren-⟦Type⟧ ρ (Forall Nat A) = cong ⟦∀⟧ (fext λ n → trans (cong Mon (ren-⟦Type⟧ (under ρ) A)) (cong (λ □ → Mon (⟦ A ⟧ty (□ , lift n))) ⟦ ρ succ⟧ren))
  ren-⟦Type⟧ ρ (Forall Linearity A) {ks} = cong ⟦∀⟧ (fext λ n → trans (cong Mon (ren-⟦Type⟧ (under ρ) A)) (cong (λ □ → Mon (⟦ A ⟧ty (□ , lift n))) ⟦ ρ succ⟧ren))
  ren-⟦Type⟧ ρ (Forall Polarity A) {ks} = cong ⟦∀⟧ (fext λ n → trans (cong Mon (ren-⟦Type⟧ (under ρ) A)) (cong (λ □ → Mon (⟦ A ⟧ty (□ , lift n))) ⟦ ρ succ⟧ren))
  ren-⟦Type⟧ ρ [ n ] = refl
  ren-⟦Type⟧ ρ (LinearityConst l) = refl
  ren-⟦Type⟧ ρ (PolarityConst p) = refl
  ren-⟦Type⟧ ρ (MaxLin l₁ l₂ l₃) =
    cong Flat (cong₃ MaxLinRel (cong lower (ren-⟦Type⟧ ρ l₁)) (cong lower (ren-⟦Type⟧ ρ l₂)) (cong lower (ren-⟦Type⟧ ρ l₃)))
  ren-⟦Type⟧ ρ (HasMul l₁ l₂ l₃) =
    cong Flat (cong₃ MulRel (cong lower (ren-⟦Type⟧ ρ l₁)) (cong lower (ren-⟦Type⟧ ρ l₂)) (cong lower (ren-⟦Type⟧ ρ l₃)))
  ren-⟦Type⟧ ρ (MaxPol p₁ p₂ p₃) =
    cong Flat (cong₃ MaxPolRel (cong lower (ren-⟦Type⟧ ρ p₁)) (cong lower (ren-⟦Type⟧ ρ p₂)) (cong lower (ren-⟦Type⟧ ρ p₃)))
  ren-⟦Type⟧ ρ (NegPol p₁ p₂) = cong Flat (cong₂ NegPolRel (cong lower (ren-⟦Type⟧ ρ p₁)) (cong lower (ren-⟦Type⟧ ρ p₂)))
  ren-⟦Type⟧ ρ (Quantify p₁ p₂) = cong Flat (cong₂ QuantifyRel (cong lower (ren-⟦Type⟧ ρ p₁)) (cong lower (ren-⟦Type⟧ ρ p₂)))

  ren-subst : ∀ {K K'}{ks : ⟦ K' ⟧kctxt} → (ρ : K' ⇒ᵣ K) → ⟦ (λ x → var (ρ x)) ⟧subst ks ≡ ⟦ ρ ⟧ren ks
  ren-subst {ε} {K'} {ks} ρ = refl
  ren-subst {K ,- κ} {K'} {ks} ρ = cong (λ □ → □ , ⟦ ρ zero ⟧tyvar ks) (ren-subst (λ x → ρ (succ x)))

  ⟦id⟧-subst : ∀ {K}{ks : ⟦ K ⟧kctxt} → ⟦ var ⟧subst ks ≡ ks
  ⟦id⟧-subst = trans (ren-subst (λ x → x)) ⟦id⟧ren

  subst-ren : ∀ {K₁ K₂ K₃} →
              (ρ : K₁ ⇒ᵣ K₂)
              (σ : K₂ ⇒ₛ K₃) →
              ∀ {ks} → ⟦ (λ x → ren-Type ρ (σ x)) ⟧subst ks ≡ ⟦ σ ⟧subst (⟦ ρ ⟧ren ks)
  subst-ren {K₁} {K₂} {ε} ρ σ = refl
  subst-ren {K₁} {K₂} {K₃ ,- ̨κ} ρ σ =
    cong₂ _,_ (subst-ren ρ (λ x → σ (succ x))) (ren-⟦Type⟧ ρ (σ zero))

  subst-⟦Type⟧ : ∀ {K K'} (σ : K' ⇒ₛ K) {κ} (A : K ⊢T κ) →
                ∀ {ks} → ⟦ subst-Type σ A ⟧ty ks ≡ ⟦ A ⟧ty (⟦ σ ⟧subst ks)
  subst-⟦Type⟧ σ (var x) = subst-⟦tyvar⟧ σ x
  subst-⟦Type⟧ σ (Bool l x) = cong₂ ⟦Bool⟧ (cong lower (subst-⟦Type⟧ σ l)) (cong lower (subst-⟦Type⟧ σ x))
  subst-⟦Type⟧ σ (Num x) = cong ⟦Num⟧ (cong lower (subst-⟦Type⟧ σ x))
  subst-⟦Type⟧ σ (A ⇒ B) = cong₂ (λ □₁ □₂ → □₁ ⟦⇒⟧ (Mon □₂)) (subst-⟦Type⟧ σ A) (subst-⟦Type⟧ σ B)
  subst-⟦Type⟧ σ (Index N) = cong ⟦Index⟧ (cong lower (subst-⟦Type⟧ σ N))
  subst-⟦Type⟧ σ (Vec N A) =
    cong₂ (λ n X → ⟦Index⟧ n ⟦⇒⟧ Mon X) (cong lower (subst-⟦Type⟧ σ N)) (subst-⟦Type⟧ σ A)
  subst-⟦Type⟧ σ (Forall Nat A) =
    cong ⟦∀⟧ (fext λ n →
      trans (cong Mon (subst-⟦Type⟧ (binder σ) A))
            (cong (λ □ → Mon (⟦ A ⟧ty (□ , lift n)))
                  (trans (subst-ren wk σ) (cong ⟦ σ ⟧subst ⟦wk⟧-eq))))
  subst-⟦Type⟧ σ (Forall Linearity A) =
    cong ⟦∀⟧ (fext λ n →
      trans (cong Mon (subst-⟦Type⟧ (binder σ) A))
            (cong (λ □ → Mon (⟦ A ⟧ty (□ , lift n)))
                  (trans (subst-ren wk σ) (cong ⟦ σ ⟧subst ⟦wk⟧-eq))))
  subst-⟦Type⟧ σ (Forall Polarity A) =
    cong ⟦∀⟧ (fext λ n →
      trans (cong Mon (subst-⟦Type⟧ (binder σ) A))
            (cong (λ □ → Mon (⟦ A ⟧ty (□ , lift n)))
                  (trans (subst-ren wk σ) (cong ⟦ σ ⟧subst ⟦wk⟧-eq))))
  subst-⟦Type⟧ σ [ n ] = refl
  subst-⟦Type⟧ σ (LinearityConst l) = refl
  subst-⟦Type⟧ σ (PolarityConst p) = refl
  subst-⟦Type⟧ ρ (MaxLin l₁ l₂ l₃) =
    cong Flat (cong₃ MaxLinRel (cong lower (subst-⟦Type⟧ ρ l₁)) (cong lower (subst-⟦Type⟧ ρ l₂)) (cong lower (subst-⟦Type⟧ ρ l₃)))
  subst-⟦Type⟧ ρ (HasMul l₁ l₂ l₃) =
    cong Flat (cong₃ MulRel (cong lower (subst-⟦Type⟧ ρ l₁)) (cong lower (subst-⟦Type⟧ ρ l₂)) (cong lower (subst-⟦Type⟧ ρ l₃)))
  subst-⟦Type⟧ ρ (MaxPol p₁ p₂ p₃) =
    cong Flat (cong₃ MaxPolRel (cong lower (subst-⟦Type⟧ ρ p₁)) (cong lower (subst-⟦Type⟧ ρ p₂)) (cong lower (subst-⟦Type⟧ ρ p₃)))
  subst-⟦Type⟧ ρ (NegPol p₁ p₂) = cong Flat (cong₂ NegPolRel (cong lower (subst-⟦Type⟧ ρ p₁)) (cong lower (subst-⟦Type⟧ ρ p₂)))
  subst-⟦Type⟧ ρ (Quantify p₁ p₂) = cong Flat (cong₂ QuantifyRel (cong lower (subst-⟦Type⟧ ρ p₁)) (cong lower (subst-⟦Type⟧ ρ p₂)))

  ------------------------------------------------------------------------------
  _×m_ : ∀ {W X Y Z} → (W ==> X) → (Y ==> Z) → (W ⟦×⟧ Y) ==> (X ⟦×⟧ Z)
  f ×m g = ⟨ f ∘ ⟦proj₁⟧ , g ∘ ⟦proj₂⟧ ⟩

  binaryM : ∀ {X Y Z} → ((X ⟦×⟧ Y) ==> Mon Z) → (Mon X ⟦×⟧ Mon Y) ==> Mon Z
  binaryM f =
      ⟦extend⟧ (⟦extend⟧ (f ∘ ⟨ ⟦proj₂⟧ , ⟦proj₁⟧ ⟩) ∘ ⟨ ⟦proj₂⟧ , ⟦proj₁⟧ ⟩)

  ternaryM : ∀ {W X Y Z} →
             ((W ⟦×⟧ (X ⟦×⟧ Y)) ==> Mon Z) → (Mon W ⟦×⟧ (Mon X ⟦×⟧ Mon Y)) ==> Mon Z
  ternaryM f = (⟦extend⟧ (⟦extend⟧ (⟦extend⟧ (f ∘ ⟨ ⟦proj₂⟧ ∘ ⟦proj₁⟧ , ⟨ ⟦proj₁⟧ ∘ ⟦proj₁⟧ , ⟦proj₂⟧ ⟩ ⟩) ∘ ⟨ ⟨ ⟦proj₂⟧ , ⟦proj₁⟧ ∘ ⟦proj₁⟧ ⟩ , ⟦proj₂⟧ ∘ ⟦proj₁⟧ ⟩) ∘ ⟨ ⟨ ⟦proj₂⟧ , ⟦proj₂⟧ ∘ ⟦proj₁⟧ ⟩ , ⟦proj₁⟧ ∘ ⟦proj₁⟧ ⟩)) ∘ ⟨ ⟦proj₂⟧ , ⟦proj₁⟧ ⟩

  seq : ∀ {X Y} → (Mon X ⟦×⟧ Mon Y) ==> Mon (X ⟦×⟧ Y)
  seq = ⟦extend⟧ ((⟦extend⟧ (⟦return⟧ ∘ ⟨ ⟦proj₂⟧ , ⟦proj₁⟧ ⟩)) ∘ ⟨ ⟦proj₂⟧ , ⟦proj₁⟧ ⟩)

  unaryM : ∀ {X Y} → (X ==> Mon Y) → Mon X ==> Mon Y
  unaryM f = ⟦extend⟧ (f ∘ ⟦proj₂⟧) ∘ ⟨ ⟦terminal⟧ , ⟦id⟧ ⟩

  ternary : ∀ {W X Y Z} →
             ((W ⟦×⟧ (X ⟦×⟧ Y)) ==> Z) → (Mon W ⟦×⟧ (Mon X ⟦×⟧ Mon Y)) ==> Mon Z
  ternary f = ternaryM (⟦return⟧ ∘ f)

  binary : ∀ {X Y Z} → ((X ⟦×⟧ Y) ==> Z) → (Mon X ⟦×⟧ Mon Y) ==> Mon Z
  binary f = binaryM (⟦return⟧ ∘ f)

  unary : ∀ {X Y} → (X ==> Y) → Mon X ==> Mon Y
  unary f = unaryM (⟦return⟧ ∘ f)

  ⟦coerce⟧ : ∀ {X Y} → X ≡ Y → X ==> Y
  ⟦coerce⟧ refl = ⟦id⟧

  ------------------------------------------------------------------------------
  ⟦_⟧ctxt : ∀ {K} → Context K → ⟦ K ⟧kctxt → ⟦Type⟧
  ⟦ ε ⟧ctxt      δ = ⟦⊤⟧
  ⟦ Γ ,- A ⟧ctxt δ = ⟦ Γ ⟧ctxt δ ⟦×⟧ ⟦ A ⟧ty δ

  ren-⟦Context⟧ : ∀ {K K'} (ρ : K' ⇒ᵣ K) (Γ : Context K) →
                  ∀ {ks} → ⟦ ren-Context ρ Γ ⟧ctxt ks ≡ ⟦ Γ ⟧ctxt (⟦ ρ ⟧ren ks)
  ren-⟦Context⟧ ρ ε = refl
  ren-⟦Context⟧ ρ (Γ ,- A) {ks} =
     trans (cong (λ □ → □ ⟦×⟧ ⟦ ren-Type ρ A ⟧ty ks) (ren-⟦Context⟧ ρ Γ))
           (cong (λ □ → ⟦ Γ ⟧ctxt (⟦ ρ ⟧ren ks) ⟦×⟧ □) (ren-⟦Type⟧ ρ A))

  ⟦_⟧var : ∀ {Δ Γ A} → Δ ⊢ Γ ∋ A → ∀ δ → ⟦ Γ ⟧ctxt δ ==> ⟦ A ⟧ty δ
  ⟦ zero ⟧var   ks = ⟦proj₂⟧
  ⟦ succ x ⟧var ks = ⟦ x ⟧var ks ∘ ⟦proj₁⟧

  ⟦_⟧tm : ∀ {Δ Γ A} → Δ / Γ ⊢ A → ∀ δ → ⟦ Γ ⟧ctxt δ ==> Mon (⟦ A ⟧ty δ)
  ⟦ var x ⟧tm δ = ⟦return⟧ ∘ ⟦ x ⟧var δ
  ⟦ ƛ t ⟧tm δ = ⟦return⟧ ∘ ⟦Λ⟧ (⟦ t ⟧tm δ)
  --   -- FIXME: if the domain type is 'Num linear', then convert this to a
  --   -- let expression, to prevent some unnecessary expansion of terms
  ⟦ s ∙ t ⟧tm δ = binaryM ⟦eval⟧ ∘ ⟨ ⟦ s ⟧tm δ , ⟦ t ⟧tm δ ⟩
  ⟦_⟧tm {Γ = Γ} (Λ Nat t) δ =
    ⟦return⟧ ∘ ⟦∀-intro⟧ (λ n → ⟦ t ⟧tm (δ , lift n) ∘ ⟦coerce⟧ (sym eq))
      where eq : ∀ {n} → ⟦ ren-Context (wk {κ = Nat}) Γ ⟧ctxt (δ , lift n) ≡ ⟦ Γ ⟧ctxt δ
            eq = trans (ren-⟦Context⟧ wk Γ) (cong (⟦ Γ ⟧ctxt) ⟦wk⟧-eq)
  ⟦_⟧tm {Γ = Γ} (Λ Linearity t) δ =
    ⟦return⟧ ∘ ⟦∀-intro⟧ (λ n → ⟦ t ⟧tm (δ , lift n) ∘ ⟦coerce⟧ (sym eq))
      where eq : ∀ {n} → ⟦ ren-Context (wk {κ = Linearity}) Γ ⟧ctxt (δ , lift n) ≡ ⟦ Γ ⟧ctxt δ
            eq = trans (ren-⟦Context⟧ wk Γ) (cong (⟦ Γ ⟧ctxt) ⟦wk⟧-eq)
  ⟦_⟧tm {Γ = Γ} (Λ Polarity t) δ =
    ⟦return⟧ ∘ ⟦∀-intro⟧ (λ n → ⟦ t ⟧tm (δ , lift n) ∘ ⟦coerce⟧ (sym eq))
      where eq : ∀ {n} → ⟦ ren-Context (wk {κ = Polarity}) Γ ⟧ctxt (δ , lift n) ≡ ⟦ Γ ⟧ctxt δ
            eq = trans (ren-⟦Context⟧ wk Γ) (cong (⟦ Γ ⟧ctxt) ⟦wk⟧-eq)
  ⟦ _•_ {s = Nat} {A = A} t N ⟧tm δ =
    (unary (⟦coerce⟧ eq) ∘ unaryM (⟦∀-elim⟧ {A = λ n → Mon (⟦ A ⟧ty (δ , lift n))} (⟦ N ⟧ty δ .lower))) ∘ ⟦ t ⟧tm δ
    where eq : ⟦ A ⟧ty (δ , ⟦ N ⟧ty δ) ≡ ⟦ subst-Type (single-sub N) A ⟧ty δ
          eq = trans (cong (λ □ → ⟦ A ⟧ty (□ , ⟦ N ⟧ty δ)) (sym ⟦id⟧-subst))
                     (sym (subst-⟦Type⟧ (single-sub N) A))
  ⟦ _•_ {s = Linearity} {A = A} t N ⟧tm δ =
    (unary (⟦coerce⟧ eq) ∘ unaryM (⟦∀-elim⟧ {A = λ n → Mon (⟦ A ⟧ty (δ , lift n))} (⟦ N ⟧ty δ .lower))) ∘ ⟦ t ⟧tm δ
    where eq : ⟦ A ⟧ty (δ , ⟦ N ⟧ty δ) ≡ ⟦ subst-Type (single-sub N) A ⟧ty δ
          eq = trans (cong (λ □ → ⟦ A ⟧ty (□ , ⟦ N ⟧ty δ)) (sym ⟦id⟧-subst))
                     (sym (subst-⟦Type⟧ (single-sub N) A))
  ⟦ _•_ {s = Polarity} {A = A} t N ⟧tm δ =
    (unary (⟦coerce⟧ eq) ∘ unaryM (⟦∀-elim⟧ {A = λ n → Mon (⟦ A ⟧ty (δ , lift n))} (⟦ N ⟧ty δ .lower))) ∘ ⟦ t ⟧tm δ
    where eq : ⟦ A ⟧ty (δ , ⟦ N ⟧ty δ) ≡ ⟦ subst-Type (single-sub N) A ⟧ty δ
          eq = trans (cong (λ □ → ⟦ A ⟧ty (□ , ⟦ N ⟧ty δ)) (sym ⟦id⟧-subst))
                     (sym (subst-⟦Type⟧ (single-sub N) A))

  ⟦ foreach n A t ⟧tm δ = ⟦return⟧ ∘ ⟦Λ⟧ (⟦ t ⟧tm δ)
    -- FIXME: two choices here:
    -- 1. Lazily do the let- and if- lifting so that it gets replicated every time we index
    --    into the array (this is what is implemented here)
    -- 2. Do all the lifting at the creation point, so it gets shared
    --
    -- The difference is manifest in the different possible
    -- implementation types for Array, specifically whether or not it
    -- includes a use of the LetLift monad.
  ⟦ index n A s t ⟧tm δ = binaryM ⟦eval⟧ ∘ ⟨ ⟦ s ⟧tm δ , ⟦ t ⟧tm δ ⟩
  ⟦ idx i ⟧tm δ = ⟦return⟧ ∘ ⟦idx⟧ _ i

  ⟦ func t ⟧tm δ = unaryM ⟦extFunc⟧ ∘ ⟦ t ⟧tm δ
  ⟦ const x ⟧tm δ = ⟦return⟧ ∘ ⟦const⟧ x
  ⟦ (t `+ t₁) t₂ ⟧tm δ = ternary ⟦add⟧ ∘ ⟨ (⟦ t ⟧tm δ) , ⟨ (⟦ t₁ ⟧tm δ) , (⟦ t₂ ⟧tm δ) ⟩ ⟩
  ⟦ (t `* t₁) t₂ ⟧tm δ = ternary ⟦mul⟧ ∘ ⟨ (⟦ t ⟧tm δ) , ⟨ (⟦ t₁ ⟧tm δ) , (⟦ t₂ ⟧tm δ) ⟩ ⟩
  ⟦ (t `≤ t₁) t₂ ⟧tm δ = ternary ⟦≤⟧ ∘ ⟨ (⟦ t ⟧tm δ) , ⟨ (⟦ t₁ ⟧tm δ) , (⟦ t₂ ⟧tm δ) ⟩ ⟩
  ⟦ if s then t else u ⟧tm δ = ⟦extend⟧ ⟦if⟧ ∘ ⟨ ⟨ ⟦ t ⟧tm δ , ⟦ u ⟧tm δ ⟩ , ⟦ s ⟧tm δ ⟩
  ⟦ (`¬ t) t₁ ⟧tm δ = binary ⟦not⟧ ∘ ⟨ ⟦ t ⟧tm δ , ⟦ t₁ ⟧tm δ ⟩
  ⟦ (t `∧ t₁) t₂ t₃ ⟧tm δ =
    (((unary ⟦and⟧ ∘ seq) ∘ (⟦id⟧ ×m seq)) ∘ (⟦id⟧ ×m (⟦id⟧ ×m seq))) ∘ ⟨ ⟦ t ⟧tm δ , ⟨ ⟦ t₁ ⟧tm δ , ⟨ ⟦ t₂ ⟧tm δ , ⟦ t₃ ⟧tm δ ⟩ ⟩ ⟩
  ⟦ (t `∨ t₁) t₂ t₃ ⟧tm δ =
    (((unary ⟦or⟧ ∘ seq) ∘ (⟦id⟧ ×m seq)) ∘ (⟦id⟧ ×m (⟦id⟧ ×m seq))) ∘ ⟨ ⟦ t ⟧tm δ , ⟨ ⟦ t₁ ⟧tm δ , ⟨ ⟦ t₂ ⟧tm δ , ⟦ t₃ ⟧tm δ ⟩ ⟩ ⟩
  ⟦ ∃ t t₁ ⟧tm δ = binary ⟦∃⟧ ∘ ⟨ ⟦ t ⟧tm δ , ⟦ t₁ ⟧tm δ ⟩

  ⟦ maxlin x ⟧tm δ = ⟦return⟧ ∘ elem x
  ⟦ hasmul x ⟧tm δ = ⟦return⟧ ∘ elem x
  ⟦ maxpol x ⟧tm δ = ⟦return⟧ ∘ elem x
  ⟦ negpol x ⟧tm δ = ⟦return⟧ ∘ elem x
  ⟦ quantify x ⟧tm δ = ⟦return⟧ ∘ elem x
