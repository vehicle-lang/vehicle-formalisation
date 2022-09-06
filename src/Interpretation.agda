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

open import MiniVehicle

record Model ℓ m : Set (suc ℓ ⊔ suc m) where
  field
    ⟦Type⟧ : Set ℓ
    _==>_ : ⟦Type⟧ → ⟦Type⟧ → Set m

    ⟦id⟧  : ∀ {X} → X ==> X
    _∘_   : ∀ {X Y Z} → Y ==> Z → X ==> Y → X ==> Z

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
    ⟦∀⟧       : (ℕ → ⟦Type⟧) → ⟦Type⟧
    ⟦∀-intro⟧ : ∀ {X A} → (∀ n → X ==> A n) → X ==> ⟦∀⟧ A
    ⟦∀-elim⟧  : ∀ {A} n → ⟦∀⟧ A ==> A n

    -- Monad
    Mon      : ⟦Type⟧ → ⟦Type⟧
    ⟦return⟧ : ∀ {X} → X ==> Mon X
    ⟦extend⟧ : ∀ {X Y Z} → ((X ⟦×⟧ Y) ==> Mon Z) → (X ⟦×⟧ Mon Y) ==> Mon Z

    -- Numbers
    ⟦Num⟧   : Linearity → ⟦Type⟧
    ⟦add⟧   : (⟦Num⟧ linear ⟦×⟧ ⟦Num⟧ linear) ==> ⟦Num⟧ linear
    ⟦mul⟧   : (⟦Num⟧ const ⟦×⟧ ⟦Num⟧ linear) ==> ⟦Num⟧ linear
    ⟦num⟧   : ∀ {X} → ℚ → X ==> ⟦Num⟧ const
    ⟦const⟧ : ⟦Num⟧ const ==> ⟦Num⟧ linear
    ⟦extFunc⟧ : ⟦Num⟧ linear ==> Mon (⟦Num⟧ linear)

    -- Booleans
    ⟦Bool⟧ : BoolKind → ⟦Type⟧
    ⟦not⟧  : ⟦Bool⟧ constraint ==> ⟦Bool⟧ constraint
    ⟦and⟧  : (⟦Bool⟧ constraint ⟦×⟧ ⟦Bool⟧ constraint) ==> ⟦Bool⟧ constraint
    ⟦or⟧   : (⟦Bool⟧ constraint ⟦×⟧ ⟦Bool⟧ constraint) ==> ⟦Bool⟧ constraint
    ⟦≤⟧    : (⟦Num⟧ linear ⟦×⟧ ⟦Num⟧ linear) ==> ⟦Bool⟧ constraint
    ⟦if⟧   : ∀ {X} → ((Mon X ⟦×⟧ Mon X) ⟦×⟧ ⟦Bool⟧ constraint) ==> Mon X
    ⟦constraint⟧ : ⟦Bool⟧ constraint ==> ⟦Bool⟧ query
    ⟦∃⟧    : (⟦Num⟧ linear ⟦⇒⟧ Mon (⟦Bool⟧ query)) ==> ⟦Bool⟧ query

    -- Indexes and Arrays
    ⟦Index⟧ : ℕ → ⟦Type⟧
    ⟦idx⟧   : (n : ℕ)(i : Fin n) → ∀ {X} → X ==> ⟦Index⟧ n

module Interpret {ℓ}{m} (ℳ : Model ℓ m) where

  open Model ℳ

  ⟦_⟧kind : Kind → Set ℓ
  ⟦ Nat ⟧kind = Lift _ ℕ
  ⟦ Type ⟧kind = ⟦Type⟧

  ⟦_⟧kctxt : KindContext → Set
  ⟦ ε ⟧kctxt      = ⊤
  ⟦ K ,-ℕ ⟧kctxt = ⟦ K ⟧kctxt × ℕ

  ⟦_⟧tyvar : ∀ {K} → K ⊢Tv → ⟦ K ⟧kctxt → ⟦ Nat ⟧kind
  ⟦ zero ⟧tyvar   (_  , n) = lift n
  ⟦ succ x ⟧tyvar (ks , _) = ⟦ x ⟧tyvar ks

  ⟦_⟧ty : ∀ {K κ} → K ⊢T κ → ⟦ K ⟧kctxt → ⟦ κ ⟧kind
  ⟦ var x ⟧ty ks = ⟦ x ⟧tyvar ks
  ⟦ Bool x ⟧ty ks = ⟦Bool⟧ x
  ⟦ Num x ⟧ty ks = ⟦Num⟧ x
  ⟦ A ⇒ B ⟧ty ks = (⟦ A ⟧ty ks) ⟦⇒⟧ Mon (⟦ B ⟧ty ks)
  ⟦ Index N ⟧ty ks = ⟦Index⟧ (⟦ N ⟧ty ks .lower)
  ⟦ Array N A ⟧ty ks = (⟦Index⟧ (⟦ N ⟧ty ks .lower)) ⟦⇒⟧ Mon (⟦ A ⟧ty ks)
  ⟦ Forall A ⟧ty ks = ⟦∀⟧ (λ n → Mon (⟦ A ⟧ty (ks , n)))
  ⟦ [ n ] ⟧ty ks    = lift n

  ⟦_⟧ren : ∀ {K K'} (ρ : K' ⇒ᵣ K) → ⟦ K' ⟧kctxt → ⟦ K ⟧kctxt
  ⟦_⟧ren {ε} ρ ks = tt
  ⟦_⟧ren {K ,-ℕ} ρ ks = ⟦_⟧ren {K} (λ x → ρ (succ x)) ks , (⟦ ρ zero ⟧tyvar ks .lower)

  ⟦_⟧subst : ∀ {K K'} → (σ : K ⊢Tv → K' ⊢T Nat) → ⟦ K' ⟧kctxt → ⟦ K ⟧kctxt
  ⟦_⟧subst {ε} σ ks = tt
  ⟦_⟧subst {K ,-ℕ} σ ks = ⟦ (λ x → σ (succ x)) ⟧subst ks , (⟦ σ zero ⟧ty ks .lower)

  ⟦_succ⟧ren : ∀ {K K'} (ρ : K' ⇒ᵣ K) →
              ∀ {ks n} → ⟦ (λ x → succ (ρ x)) ⟧ren (ks , n) ≡ ⟦ ρ ⟧ren ks
  ⟦_succ⟧ren {ε} ρ = refl
  ⟦_succ⟧ren {K ,-ℕ} ρ {ks} =
    cong (λ □ → (□ , ⟦ ρ zero ⟧tyvar ks .lower)) ⟦ (λ x → ρ (succ x)) succ⟧ren

  ren-⟦tyvar⟧ : ∀ {K K'} (ρ : K' ⇒ᵣ K) (x : K ⊢Tv) →
               ∀ {ks} → ⟦ ρ x ⟧tyvar ks ≡ ⟦ x ⟧tyvar (⟦ ρ ⟧ren ks)
  ren-⟦tyvar⟧ ρ zero     = cong lift refl
  ren-⟦tyvar⟧ ρ (succ x) = ren-⟦tyvar⟧ (λ x → ρ (succ x)) x

  subst-⟦tyvar⟧ : ∀ {K K'} (σ : K ⊢Tv → K' ⊢T Nat) (x : K ⊢Tv) →
                 ∀ {ks} → ⟦ σ x ⟧ty ks ≡ ⟦ x ⟧tyvar (⟦ σ ⟧subst ks)
  subst-⟦tyvar⟧ σ zero     = refl
  subst-⟦tyvar⟧ σ (succ x) = subst-⟦tyvar⟧ (λ x → σ (succ x)) x

  ren-∘ : ∀ {K₁ K₂ K₃} (ρ₁ : K₁ ⇒ᵣ K₂)(ρ₂ : K₂ ⇒ᵣ K₃) →
         ∀ ks → ⟦ (λ x → ρ₁ (ρ₂ x)) ⟧ren ks ≡ ⟦ ρ₂ ⟧ren (⟦ ρ₁ ⟧ren ks)
  ren-∘ {K₁} {K₂} {ε} ρ₁ ρ₂ ks = refl
  ren-∘ {K₁} {K₂} {K₃ ,-ℕ} ρ₁ ρ₂ ks =
    trans (cong (λ □ → □ , ⟦ ρ₁ (ρ₂ zero) ⟧tyvar ks .lower)
                (ren-∘ ρ₁ (λ x → ρ₂ (succ x)) ks))
          (cong (λ □ → ⟦ (λ x → ρ₂ (succ x)) ⟧ren (⟦ ρ₁ ⟧ren ks) , □)
                (cong lower (ren-⟦tyvar⟧ ρ₁ (ρ₂ zero))))

  ⟦id⟧ren : ∀ {K}{ks : ⟦ K ⟧kctxt} → ⟦ (λ x → x) ⟧ren ks ≡ ks
  ⟦id⟧ren {ε} {ks} = refl
  ⟦id⟧ren {K ,-ℕ} {ks , n} = cong (λ □ → □ , n) (trans (⟦ (λ x → x) succ⟧ren {ks}) ⟦id⟧ren)

  ⟦wk⟧-eq : ∀ {K}{ks : ⟦ K ,-ℕ ⟧kctxt} → ⟦ wk ⟧ren ks ≡ ks .proj₁
  ⟦wk⟧-eq {K}{ks , n} = trans (⟦ (λ x → x) succ⟧ren {ks}) ⟦id⟧ren

  ren-⟦Type⟧ : ∀ {K K'} (ρ : K' ⇒ᵣ K) {κ} (A : K ⊢T κ) →
             ∀ {ks} → ⟦ ren-Type ρ A ⟧ty ks ≡ ⟦ A ⟧ty (⟦ ρ ⟧ren ks)
  ren-⟦Type⟧ ρ (var x) = ren-⟦tyvar⟧ ρ x
  ren-⟦Type⟧ ρ (Bool x) = refl
  ren-⟦Type⟧ ρ (Num x) = refl
  ren-⟦Type⟧ ρ (A ⇒ B) =
    cong₂ (λ □₁ □₂ → □₁ ⟦⇒⟧ (Mon □₂)) (ren-⟦Type⟧ ρ A) (ren-⟦Type⟧ ρ B)
  ren-⟦Type⟧ ρ (Index N) =
    cong (λ □ → ⟦Index⟧ (□ .lower)) (ren-⟦Type⟧ ρ N)
  ren-⟦Type⟧ ρ (Array N A) =
    cong₂ (λ □₁ □₂ → ⟦Index⟧ (□₁ .lower) ⟦⇒⟧ (Mon □₂)) (ren-⟦Type⟧ ρ N) (ren-⟦Type⟧ ρ A)
  ren-⟦Type⟧ ρ (Forall A) {ks} =
    cong ⟦∀⟧ (fext λ n → trans (cong Mon (ren-⟦Type⟧ (under ρ) A)) (cong (λ □ → Mon (⟦ A ⟧ty (□ , n))) ⟦ ρ succ⟧ren))
  ren-⟦Type⟧ ρ [ n ] = refl

  ren-subst : ∀ {K K'}{ks : ⟦ K' ⟧kctxt} → (ρ : K' ⇒ᵣ K) → ⟦ (λ x → var (ρ x)) ⟧subst ks ≡ ⟦ ρ ⟧ren ks
  ren-subst {ε} {K'} {ks} ρ = refl
  ren-subst {K ,-ℕ} {K'} {ks} ρ = cong (λ □ → □ , ⟦ ρ zero ⟧tyvar ks .lower) (ren-subst (λ x → ρ (succ x)))

  ⟦id⟧-subst : ∀ {K}{ks : ⟦ K ⟧kctxt} → ⟦ var ⟧subst ks ≡ ks
  ⟦id⟧-subst = trans (ren-subst (λ x → x)) ⟦id⟧ren

  subst-ren : ∀ {K₁ K₂ K₃} →
              (ρ : K₁ ⇒ᵣ K₂)
              (σ : K₃ ⊢Tv → K₂ ⊢T Nat) →
              ∀ {ks} → ⟦ (λ x → ren-Type ρ (σ x)) ⟧subst ks ≡ ⟦ σ ⟧subst (⟦ ρ ⟧ren ks)
  subst-ren {K₁} {K₂} {ε} ρ σ = refl
  subst-ren {K₁} {K₂} {K₃ ,-ℕ} ρ σ =
    cong₂ _,_ (subst-ren ρ (λ x → σ (succ x))) (cong lower (ren-⟦Type⟧ ρ (σ zero)))

  subst-⟦Type⟧ : ∀ {K K'} (σ : K ⊢Tv → K' ⊢T Nat) {κ} (A : K ⊢T κ) →
                ∀ {ks} → ⟦ subst-Type σ A ⟧ty ks ≡ ⟦ A ⟧ty (⟦ σ ⟧subst ks)
  subst-⟦Type⟧ σ (var x) = subst-⟦tyvar⟧ σ x
  subst-⟦Type⟧ σ (Bool x) = refl
  subst-⟦Type⟧ σ (Num x) = refl
  subst-⟦Type⟧ σ (A ⇒ B) = cong₂ (λ □₁ □₂ → □₁ ⟦⇒⟧ (Mon □₂)) (subst-⟦Type⟧ σ A) (subst-⟦Type⟧ σ B)
  subst-⟦Type⟧ σ (Index N) = cong ⟦Index⟧ (cong lower (subst-⟦Type⟧ σ N))
  subst-⟦Type⟧ σ (Array N A) =
    cong₂ (λ n X → ⟦Index⟧ n ⟦⇒⟧ Mon X) (cong lower (subst-⟦Type⟧ σ N)) (subst-⟦Type⟧ σ A)
  subst-⟦Type⟧ σ (Forall A) =
    cong ⟦∀⟧ (fext λ n →
      trans (cong Mon (subst-⟦Type⟧ (binder σ) A))
            (cong (λ □ → Mon (⟦ A ⟧ty (□ , n)))
                  (trans (subst-ren wk σ) (cong ⟦ σ ⟧subst ⟦wk⟧-eq))))
  subst-⟦Type⟧ σ [ n ] = refl

  ------------------------------------------------------------------------------
  binaryM : ∀ {X Y Z} → ((X ⟦×⟧ Y) ==> Mon Z) → (Mon X ⟦×⟧ Mon Y) ==> Mon Z
  binaryM f =
      ⟦extend⟧ (⟦extend⟧ (f ∘ ⟨ ⟦proj₂⟧ , ⟦proj₁⟧ ⟩) ∘ ⟨ ⟦proj₂⟧ , ⟦proj₁⟧ ⟩)

  unaryM : ∀ {X Y} → (X ==> Mon Y) → Mon X ==> Mon Y
  unaryM f = ⟦extend⟧ (f ∘ ⟦proj₂⟧) ∘ ⟨ ⟦terminal⟧ , ⟦id⟧ ⟩

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
  ⟦_⟧tm {Γ = Γ} (Λ t) δ =
    ⟦return⟧ ∘ ⟦∀-intro⟧ (λ n → ⟦ t ⟧tm (δ , n) ∘ ⟦coerce⟧ (sym eq))
      where eq : ∀ {n} → ⟦ ren-Context wk Γ ⟧ctxt (δ , n) ≡ ⟦ Γ ⟧ctxt δ
            eq = trans (ren-⟦Context⟧ wk Γ) (cong (⟦ Γ ⟧ctxt) ⟦wk⟧-eq)
  ⟦ _•_ {A = A} t N ⟧tm δ =
    (unary (⟦coerce⟧ eq) ∘ unaryM (⟦∀-elim⟧ {λ n → Mon (⟦ A ⟧ty (δ , n))} (⟦ N ⟧ty δ .lower))) ∘ ⟦ t ⟧tm δ
    where eq : ⟦ A ⟧ty (δ , ⟦ N ⟧ty δ .lower) ≡ ⟦ subst-Type (single-sub N) A ⟧ty δ
          eq = trans (cong (λ □ → ⟦ A ⟧ty (□ , ⟦ N ⟧ty δ .lower)) (sym ⟦id⟧-subst))
                     (sym (subst-⟦Type⟧ (single-sub N) A))
  ⟦ func t ⟧tm δ = unaryM ⟦extFunc⟧ ∘ ⟦ t ⟧tm δ
  ⟦ const q ⟧tm δ = ⟦return⟧ ∘ (⟦num⟧ q)
  ⟦ lift t ⟧tm δ = unary ⟦const⟧ ∘ (⟦ t ⟧tm δ)
  ⟦ t₁ `+ t₂ ⟧tm δ = binary ⟦add⟧ ∘ ⟨ ⟦ t₁ ⟧tm δ , ⟦ t₂ ⟧tm δ ⟩
  ⟦ t₁ `* t₂ ⟧tm  δ = binary ⟦mul⟧ ∘ ⟨ ⟦ t₁ ⟧tm δ , ⟦ t₂ ⟧tm δ ⟩
  ⟦ array n A t ⟧tm δ = ⟦return⟧ ∘ ⟦Λ⟧ (⟦ t ⟧tm δ)
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

  ⟦ t₁ `≤ t₂ ⟧tm δ = binary ⟦≤⟧ ∘ ⟨ ⟦ t₁ ⟧tm δ , ⟦ t₂ ⟧tm δ ⟩
  ⟦ if s then t else u ⟧tm δ = ⟦extend⟧ ⟦if⟧ ∘ ⟨ ⟨ ⟦ t ⟧tm δ , ⟦ u ⟧tm δ ⟩ , ⟦ s ⟧tm δ ⟩
  ⟦ `¬ t ⟧tm δ = unary ⟦not⟧ ∘ ⟦ t ⟧tm δ
  ⟦ t₁ `∧ t₂ ⟧tm δ = binary ⟦and⟧ ∘ ⟨ ⟦ t₁ ⟧tm δ , ⟦ t₂ ⟧tm δ ⟩
  ⟦ t₁ `∨ t₂ ⟧tm δ = binary ⟦or⟧ ∘ ⟨ ⟦ t₁ ⟧tm δ , ⟦ t₂ ⟧tm δ ⟩
  ⟦ constraint t ⟧tm δ = unary ⟦constraint⟧ ∘ ⟦ t ⟧tm δ
  ⟦ ∃ t ⟧tm δ = unary ⟦∃⟧ ∘ ⟦ t ⟧tm δ
