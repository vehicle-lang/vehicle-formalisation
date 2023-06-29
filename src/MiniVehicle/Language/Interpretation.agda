
open import MiniVehicle.Language.Syntax.Restriction
open import MiniVehicle.Language.Model

module MiniVehicle.Language.Interpretation {ℓ}{m} (R : Restriction) (ℳ : Model R ℓ m) where

open import Level using (suc; 0ℓ; _⊔_; Lift; lift; lower)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Rational using (ℚ)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality
            using (_≡_; refl; cong; trans; cong₂; sym)

open import Util

open Restriction R
open import MiniVehicle.Language.Syntax R
open Model ℳ

-- FIXME: try to remove this by defining setoid equalities for each kind
postulate
  fext : ∀ {ℓ₁ ℓ₂}{A : Set ℓ₁}{B : A → Set ℓ₂}{f g : (a : A) → B a} →
         ((a : A) → f a ≡ g a) → f ≡ g


⟦_⟧kind : Kind → Set ℓ
⟦ Nat ⟧kind = Lift _ ℕ
⟦ NumRes ⟧kind = Lift _ NumRestriction
⟦ BoolRes ⟧kind = Lift _ BoolRestriction
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
⟦ Bool r ⟧ty ks = ⟦Bool⟧ (⟦ r ⟧ty ks .lower)
⟦ Num r ⟧ty ks = ⟦Num⟧ (⟦ r ⟧ty ks .lower)
⟦ A ⇒ B ⟧ty ks = (⟦ A ⟧ty ks) ⟦⇒⟧ Mon (⟦ B ⟧ty ks)
⟦ Index N ⟧ty ks = ⟦Index⟧ (⟦ N ⟧ty ks .lower)
⟦ Vec N A ⟧ty ks = (⟦Index⟧ (⟦ N ⟧ty ks .lower)) ⟦⇒⟧ Mon (⟦ A ⟧ty ks)
⟦ Forall Nat A ⟧ty ks = ⟦∀⟧ (λ n → Mon (⟦ A ⟧ty (ks , lift n)))
⟦ Forall NumRes A ⟧ty ks = ⟦∀⟧ (λ l → Mon (⟦ A ⟧ty (ks , lift l)))
⟦ Forall BoolRes A ⟧ty ks = ⟦∀⟧ (λ p → Mon (⟦ A ⟧ty (ks , lift p)))
⟦ [ n ] ⟧ty ks = lift n
-- Number restrictions
⟦ NumRes n ⟧ty ks = lift n
⟦ NumConstRes n ⟧ty ks = Flat (NumConstRestriction (⟦ n ⟧ty ks .lower))
⟦ FuncRes n₁ n₂ ⟧ty ks = Flat (FuncRestriction (⟦ n₁ ⟧ty ks .lower) (⟦ n₂ ⟧ty ks .lower))
⟦ AddRes l₁ l₂ l₃ ⟧ty ks =
  Flat (AddRestriction (⟦ l₁ ⟧ty ks .lower) (⟦ l₂ ⟧ty ks .lower) (⟦ l₃ ⟧ty ks .lower))
⟦ MulRes l₁ l₂ l₃ ⟧ty ks =
  Flat (MulRestriction (⟦ l₁ ⟧ty ks .lower) (⟦ l₂ ⟧ty ks .lower) (⟦ l₃ ⟧ty ks .lower))
-- Bool restrictions
⟦ BoolRes b ⟧ty ks = lift b
⟦ BoolConstRes b ⟧ty ks = Flat (BoolConstRestriction (⟦ b ⟧ty ks .lower))
⟦ NotRes n₁ n₂ ⟧ty ks = Flat (NotRestriction (⟦ n₁ ⟧ty ks .lower) (⟦ n₂ ⟧ty ks .lower))
⟦ AndRes l₁ l₂ l₃ ⟧ty ks =
  Flat (AndRestriction (⟦ l₁ ⟧ty ks .lower) (⟦ l₂ ⟧ty ks .lower) (⟦ l₃ ⟧ty ks .lower))
⟦ OrRes l₁ l₂ l₃ ⟧ty ks =
  Flat (OrRestriction (⟦ l₁ ⟧ty ks .lower) (⟦ l₂ ⟧ty ks .lower) (⟦ l₃ ⟧ty ks .lower))
⟦ CompRes l₁ l₂ l₃ ⟧ty ks =
  Flat (CompRestriction (⟦ l₁ ⟧ty ks .lower) (⟦ l₂ ⟧ty ks .lower) (⟦ l₃ ⟧ty ks .lower))
⟦ QuantRes n p₁ p₂ ⟧ty ks =
  Flat (QuantRestriction (⟦ n ⟧ty ks .lower) (⟦ p₁ ⟧ty ks .lower) (⟦ p₂ ⟧ty ks .lower))
⟦ IfRes b ⟧ty ks =
  Flat (IfRestriction (⟦ b ⟧ty ks .lower))

⟦_⟧subst : ∀ {K K'} → (K' ⇒ₛ K) → ⟦ K' ⟧kctxt → ⟦ K ⟧kctxt
⟦_⟧subst {ε} σ ks = lift tt
⟦_⟧subst {K ,- κ} σ ks = ⟦ (λ x → σ (succ x)) ⟧subst ks , ⟦ σ zero ⟧ty ks

⟦_succ⟧ren : ∀ {K K'} (ρ : K' ⇒ᵣ K) →
            ∀ {ks κ v} →
            ⟦ (λ x → succ {κ′ = κ} (ρ x)) ⟧ren (ks , v) ≡ ⟦ ρ ⟧ren ks
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
ren-⟦Type⟧ ρ (Bool r) = cong ⟦Bool⟧ (cong lower (ren-⟦Type⟧ ρ r))
ren-⟦Type⟧ ρ (Num r) = cong ⟦Num⟧ (cong lower (ren-⟦Type⟧ ρ r))
ren-⟦Type⟧ ρ (A ⇒ B) =
  cong₂ (λ □₁ □₂ → □₁ ⟦⇒⟧ (Mon □₂)) (ren-⟦Type⟧ ρ A) (ren-⟦Type⟧ ρ B)
ren-⟦Type⟧ ρ (Index N) =
  cong (λ □ → ⟦Index⟧ (□ .lower)) (ren-⟦Type⟧ ρ N)
ren-⟦Type⟧ ρ (Vec N A) =
  cong₂ (λ □₁ □₂ → ⟦Index⟧ (□₁ .lower) ⟦⇒⟧ (Mon □₂)) (ren-⟦Type⟧ ρ N) (ren-⟦Type⟧ ρ A)
ren-⟦Type⟧ ρ (Forall Nat A) = cong ⟦∀⟧ (fext λ n → trans (cong Mon (ren-⟦Type⟧ (under ρ) A)) (cong (λ □ → Mon (⟦ A ⟧ty (□ , lift n))) ⟦ ρ succ⟧ren))
ren-⟦Type⟧ ρ (Forall NumRes A) {ks} = cong ⟦∀⟧ (fext λ n → trans (cong Mon (ren-⟦Type⟧ (under ρ) A)) (cong (λ □ → Mon (⟦ A ⟧ty (□ , lift n))) ⟦ ρ succ⟧ren))
ren-⟦Type⟧ ρ (Forall BoolRes A) {ks} = cong ⟦∀⟧ (fext λ n → trans (cong Mon (ren-⟦Type⟧ (under ρ) A)) (cong (λ □ → Mon (⟦ A ⟧ty (□ , lift n))) ⟦ ρ succ⟧ren))
ren-⟦Type⟧ ρ [ n ] = refl
-- Number restrictions
ren-⟦Type⟧ ρ (NumRes l) = refl
ren-⟦Type⟧ ρ (NumConstRes l) =
  cong Flat (cong NumConstRestriction (cong lower (ren-⟦Type⟧ ρ l)))
ren-⟦Type⟧ ρ (FuncRes l₁ l₂) =
  cong Flat (cong₂ FuncRestriction (cong lower (ren-⟦Type⟧ ρ l₁)) (cong lower (ren-⟦Type⟧ ρ l₂)))
ren-⟦Type⟧ ρ (AddRes l₁ l₂ l₃) =
  cong Flat (cong₃ AddRestriction (cong lower (ren-⟦Type⟧ ρ l₁)) (cong lower (ren-⟦Type⟧ ρ l₂)) (cong lower (ren-⟦Type⟧ ρ l₃)))
ren-⟦Type⟧ ρ (MulRes l₁ l₂ l₃) =
  cong Flat (cong₃ MulRestriction (cong lower (ren-⟦Type⟧ ρ l₁)) (cong lower (ren-⟦Type⟧ ρ l₂)) (cong lower (ren-⟦Type⟧ ρ l₃)))
-- Bool restrictions
ren-⟦Type⟧ ρ (BoolRes p) = refl
ren-⟦Type⟧ ρ (BoolConstRes l) =
  cong Flat (cong BoolConstRestriction (cong lower (ren-⟦Type⟧ ρ l)))
ren-⟦Type⟧ ρ (NotRes l₁ l₂) =
  cong Flat (cong₂ NotRestriction (cong lower (ren-⟦Type⟧ ρ l₁)) (cong lower (ren-⟦Type⟧ ρ l₂)))
ren-⟦Type⟧ ρ (AndRes l₁ l₂ l₃) =
  cong Flat (cong₃ AndRestriction (cong lower (ren-⟦Type⟧ ρ l₁)) (cong lower (ren-⟦Type⟧ ρ l₂)) (cong lower (ren-⟦Type⟧ ρ l₃)))
ren-⟦Type⟧ ρ (OrRes l₁ l₂ l₃) =
  cong Flat (cong₃ OrRestriction (cong lower (ren-⟦Type⟧ ρ l₁)) (cong lower (ren-⟦Type⟧ ρ l₂)) (cong lower (ren-⟦Type⟧ ρ l₃)))
ren-⟦Type⟧ ρ (CompRes l₁ l₂ l₃) =
  cong Flat (cong₃ CompRestriction (cong lower (ren-⟦Type⟧ ρ l₁)) (cong lower (ren-⟦Type⟧ ρ l₂)) (cong lower (ren-⟦Type⟧ ρ l₃)))
ren-⟦Type⟧ ρ (QuantRes l₁ l₂ l₃) =
  cong Flat (cong₃ QuantRestriction (cong lower (ren-⟦Type⟧ ρ l₁)) (cong lower (ren-⟦Type⟧ ρ l₂)) (cong lower (ren-⟦Type⟧ ρ l₃)))
ren-⟦Type⟧ ρ (IfRes l) =
  cong Flat (cong IfRestriction (cong lower (ren-⟦Type⟧ ρ l)))

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
subst-⟦Type⟧ σ (Bool r) = cong ⟦Bool⟧ (cong lower (subst-⟦Type⟧ σ r))
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
subst-⟦Type⟧ σ (Forall NumRes A) =
  cong ⟦∀⟧ (fext λ n →
    trans (cong Mon (subst-⟦Type⟧ (binder σ) A))
          (cong (λ □ → Mon (⟦ A ⟧ty (□ , lift n)))
                (trans (subst-ren wk σ) (cong ⟦ σ ⟧subst ⟦wk⟧-eq))))
subst-⟦Type⟧ σ (Forall BoolRes A) =
  cong ⟦∀⟧ (fext λ n →
    trans (cong Mon (subst-⟦Type⟧ (binder σ) A))
          (cong (λ □ → Mon (⟦ A ⟧ty (□ , lift n)))
                (trans (subst-ren wk σ) (cong ⟦ σ ⟧subst ⟦wk⟧-eq))))
subst-⟦Type⟧ σ [ n ] = refl
-- Number constraints
subst-⟦Type⟧ σ (NumRes l) = refl
subst-⟦Type⟧ σ (NumConstRes l) =
  cong Flat (cong NumConstRestriction (cong lower (subst-⟦Type⟧ σ l)))
subst-⟦Type⟧ σ (FuncRes p₁ p₂) =
  cong Flat (cong₂ FuncRestriction (cong lower (subst-⟦Type⟧ σ p₁)) (cong lower (subst-⟦Type⟧ σ p₂)))
subst-⟦Type⟧ σ (AddRes l₁ l₂ l₃) =
  cong Flat (cong₃ AddRestriction (cong lower (subst-⟦Type⟧ σ l₁)) (cong lower (subst-⟦Type⟧ σ l₂)) (cong lower (subst-⟦Type⟧ σ l₃)))
subst-⟦Type⟧ σ (MulRes l₁ l₂ l₃) =
  cong Flat (cong₃ MulRestriction (cong lower (subst-⟦Type⟧ σ l₁)) (cong lower (subst-⟦Type⟧ σ l₂)) (cong lower (subst-⟦Type⟧ σ l₃)))

-- Bool constraints
subst-⟦Type⟧ σ (BoolRes l) = refl
subst-⟦Type⟧ σ (BoolConstRes l) =
  cong Flat (cong BoolConstRestriction (cong lower (subst-⟦Type⟧ σ l)))
subst-⟦Type⟧ σ (NotRes p₁ p₂) =
  cong Flat (cong₂ NotRestriction (cong lower (subst-⟦Type⟧ σ p₁)) (cong lower (subst-⟦Type⟧ σ p₂)))
subst-⟦Type⟧ σ (AndRes l₁ l₂ l₃) =
  cong Flat (cong₃ AndRestriction (cong lower (subst-⟦Type⟧ σ l₁)) (cong lower (subst-⟦Type⟧ σ l₂)) (cong lower (subst-⟦Type⟧ σ l₃)))
subst-⟦Type⟧ σ (OrRes l₁ l₂ l₃) =
  cong Flat (cong₃ OrRestriction (cong lower (subst-⟦Type⟧ σ l₁)) (cong lower (subst-⟦Type⟧ σ l₂)) (cong lower (subst-⟦Type⟧ σ l₃)))
subst-⟦Type⟧ σ (CompRes l₁ l₂ l₃) =
  cong Flat (cong₃ CompRestriction (cong lower (subst-⟦Type⟧ σ l₁)) (cong lower (subst-⟦Type⟧ σ l₂)) (cong lower (subst-⟦Type⟧ σ l₃)))
subst-⟦Type⟧ σ (QuantRes l₁ l₂ l₃) =
  cong Flat (cong₃ QuantRestriction (cong lower (subst-⟦Type⟧ σ l₁)) (cong lower (subst-⟦Type⟧ σ l₂)) (cong lower (subst-⟦Type⟧ σ l₃)))
subst-⟦Type⟧ σ (IfRes b) =
  cong Flat (cong IfRestriction (cong lower (subst-⟦Type⟧ σ b)))

------------------------------------------------------------------------------
_×m_ : ∀ {W X Y Z} → (W ==> X) → (Y ==> Z) → (W ⟦×⟧ Y) ==> (X ⟦×⟧ Z)
f ×m g = ⟨ f ∘ ⟦proj₁⟧ , g ∘ ⟦proj₂⟧ ⟩

seq : ∀ {X Y} → (Mon X ⟦×⟧ Mon Y) ==> Mon (X ⟦×⟧ Y)
seq = ⟦extend⟧ ((⟦extend⟧ (⟦return⟧ ∘ ⟨ ⟦proj₂⟧ , ⟦proj₁⟧ ⟩)) ∘ ⟨ ⟦proj₂⟧ , ⟦proj₁⟧ ⟩)

ternaryM : ∀ {W X Y Z} →
           ((W ⟦×⟧ (X ⟦×⟧ Y)) ==> Mon Z) → (Mon W ⟦×⟧ (Mon X ⟦×⟧ Mon Y)) ==> Mon Z
ternaryM f = (⟦extend⟧ (⟦extend⟧ (⟦extend⟧ (f ∘ ⟨ ⟦proj₂⟧ ∘ ⟦proj₁⟧ , ⟨ ⟦proj₁⟧ ∘ ⟦proj₁⟧ , ⟦proj₂⟧ ⟩ ⟩) ∘ ⟨ ⟨ ⟦proj₂⟧ , ⟦proj₁⟧ ∘ ⟦proj₁⟧ ⟩ , ⟦proj₂⟧ ∘ ⟦proj₁⟧ ⟩) ∘ ⟨ ⟨ ⟦proj₂⟧ , ⟦proj₂⟧ ∘ ⟦proj₁⟧ ⟩ , ⟦proj₁⟧ ∘ ⟦proj₁⟧ ⟩)) ∘ ⟨ ⟦proj₂⟧ , ⟦proj₁⟧ ⟩

binaryM : ∀ {X Y Z} → ((X ⟦×⟧ Y) ==> Mon Z) → (Mon X ⟦×⟧ Mon Y) ==> Mon Z
binaryM f =
    ⟦extend⟧ (⟦extend⟧ (f ∘ ⟨ ⟦proj₂⟧ , ⟦proj₁⟧ ⟩) ∘ ⟨ ⟦proj₂⟧ , ⟦proj₁⟧ ⟩)

unaryM : ∀ {X Y} → (X ==> Mon Y) → Mon X ==> Mon Y
unaryM f = ⟦extend⟧ (f ∘ ⟦proj₂⟧) ∘ ⟨ ⟦terminal⟧ , ⟦id⟧ ⟩

ternary : ∀ {W X Y Z} →
           ((W ⟦×⟧ (X ⟦×⟧ Y)) ==> Z) → (Mon W ⟦×⟧ (Mon X ⟦×⟧ Mon Y)) ==> Mon Z
ternary f = ternaryM (⟦return⟧ ∘ f)

binary : ∀ {X Y Z} → ((X ⟦×⟧ Y) ==> Z) → (Mon X ⟦×⟧ Mon Y) ==> Mon Z
binary f = binaryM (⟦return⟧ ∘ f)

unary : ∀ {X Y} → (X ==> Y) → Mon X ==> Mon Y
unary f = unaryM (⟦return⟧ ∘ f)

⟦elem⟧ : ∀ {X A} → A → X ==> Mon (Flat A)
⟦elem⟧ r = ⟦return⟧ ∘ elem r

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
⟦_⟧tm {Γ = Γ} (Λ NumRes t) δ =
  ⟦return⟧ ∘ ⟦∀-intro⟧ (λ n → ⟦ t ⟧tm (δ , lift n) ∘ ⟦coerce⟧ (sym eq))
    where eq : ∀ {n} → ⟦ ren-Context (wk {κ = NumRes}) Γ ⟧ctxt (δ , lift n) ≡ ⟦ Γ ⟧ctxt δ
          eq = trans (ren-⟦Context⟧ wk Γ) (cong (⟦ Γ ⟧ctxt) ⟦wk⟧-eq)
⟦_⟧tm {Γ = Γ} (Λ BoolRes t) δ =
  ⟦return⟧ ∘ ⟦∀-intro⟧ (λ n → ⟦ t ⟧tm (δ , lift n) ∘ ⟦coerce⟧ (sym eq))
    where eq : ∀ {n} → ⟦ ren-Context (wk {κ = BoolRes}) Γ ⟧ctxt (δ , lift n) ≡ ⟦ Γ ⟧ctxt δ
          eq = trans (ren-⟦Context⟧ wk Γ) (cong (⟦ Γ ⟧ctxt) ⟦wk⟧-eq)
⟦ _•_ {s = Nat} {A = A} t N ⟧tm δ =
  (unary (⟦coerce⟧ eq) ∘ unaryM (⟦∀-elim⟧ {A = λ n → Mon (⟦ A ⟧ty (δ , lift n))} (⟦ N ⟧ty δ .lower))) ∘ ⟦ t ⟧tm δ
  where eq : ⟦ A ⟧ty (δ , ⟦ N ⟧ty δ) ≡ ⟦ subst-Type (single-sub N) A ⟧ty δ
        eq = trans (cong (λ □ → ⟦ A ⟧ty (□ , ⟦ N ⟧ty δ)) (sym ⟦id⟧-subst))
                   (sym (subst-⟦Type⟧ (single-sub N) A))
⟦ _•_ {s = NumRes} {A = A} t N ⟧tm δ =
  (unary (⟦coerce⟧ eq) ∘ unaryM (⟦∀-elim⟧ {A = λ n → Mon (⟦ A ⟧ty (δ , lift n))} (⟦ N ⟧ty δ .lower))) ∘ ⟦ t ⟧tm δ
  where eq : ⟦ A ⟧ty (δ , ⟦ N ⟧ty δ) ≡ ⟦ subst-Type (single-sub N) A ⟧ty δ
        eq = trans (cong (λ □ → ⟦ A ⟧ty (□ , ⟦ N ⟧ty δ)) (sym ⟦id⟧-subst))
                   (sym (subst-⟦Type⟧ (single-sub N) A))
⟦ _•_ {s = BoolRes} {A = A} t N ⟧tm δ =
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

⟦ func r t ⟧tm δ = binaryM ⟦extFunc⟧ ∘ ⟨ ⟦ r ⟧tm δ , ⟦ t ⟧tm δ ⟩
⟦ const r x ⟧tm δ = unary (⟦const⟧ x) ∘ ⟦ r ⟧tm δ
⟦ _`+_ r t₁ t₂ ⟧tm δ = ternary ⟦add⟧ ∘  ⟨ ⟦ r ⟧tm δ , ⟨ (⟦ t₁ ⟧tm δ) , (⟦ t₂ ⟧tm δ) ⟩ ⟩

⟦ _`*_ r t₁ t₂ ⟧tm δ = ternary ⟦mul⟧ ∘  ⟨ ⟦ r ⟧tm δ , ⟨ (⟦ t₁ ⟧tm δ) , (⟦ t₂ ⟧tm δ) ⟩ ⟩
⟦ _`≤_ r t₁ t₂ ⟧tm δ = ternary ⟦≤⟧ ∘  ⟨ ⟦ r ⟧tm δ , ⟨ (⟦ t₁ ⟧tm δ) , (⟦ t₂ ⟧tm δ) ⟩ ⟩
⟦ _`<_ r t₁ t₂ ⟧tm δ = ternary ⟦<⟧ ∘  ⟨ ⟦ r ⟧tm δ , ⟨ (⟦ t₁ ⟧tm δ) , (⟦ t₂ ⟧tm δ) ⟩ ⟩
⟦_⟧tm {Γ = Γ} (if_then_else_ r b t u) δ = ⟦extend⟧ ⟦if⟧ ∘ ⟨ ⟨ ⟦ t ⟧tm δ , ⟦ u ⟧tm δ ⟩ , seq ∘ ⟨ ⟦ r ⟧tm δ , ⟦ b ⟧tm δ ⟩ ⟩
⟦ `¬_ r t ⟧tm δ = binary ⟦not⟧ ∘ ⟨ ⟦ r ⟧tm δ , ⟦ t ⟧tm δ ⟩
⟦ _`∧_ r t₁ t₂ ⟧tm δ = ternary ⟦and⟧ ∘ ⟨ ⟦ r ⟧tm δ , ⟨ (⟦ t₁ ⟧tm δ) , (⟦ t₂ ⟧tm δ) ⟩ ⟩
⟦ _`∨_ r t₁ t₂ ⟧tm δ = ternary ⟦or⟧ ∘ ⟨ ⟦ r ⟧tm δ , ⟨ (⟦ t₁ ⟧tm δ) , (⟦ t₂ ⟧tm δ) ⟩ ⟩
⟦ ∃ t t₁ ⟧tm δ = binary ⟦∃⟧ ∘ ⟨ ⟦ t ⟧tm δ , ⟦ t₁ ⟧tm δ ⟩

⟦ numConstRes n ⟧tm δ = ⟦return⟧ ∘ elem n
⟦ funcRes n ⟧tm δ = ⟦return⟧ ∘ elem n
⟦ addRes n ⟧tm δ = ⟦return⟧ ∘ elem n
⟦ mulRes n ⟧tm δ = ⟦return⟧ ∘ elem n

⟦ boolConstRes n ⟧tm δ = ⟦return⟧ ∘ elem n
⟦ notRes n ⟧tm δ = ⟦return⟧ ∘ elem n
⟦ andRes n ⟧tm δ = ⟦return⟧ ∘ elem n
⟦ orRes n ⟧tm δ = ⟦return⟧ ∘ elem n
⟦ compRes n ⟧tm δ = ⟦return⟧ ∘ elem n
⟦ quantRes n ⟧tm δ = ⟦return⟧ ∘ elem n
⟦ ifRes n ⟧tm δ = ⟦return⟧ ∘ elem n
