module vehicle where

open import Level using (0ℓ; Lift; lift; lower)
open import Level.Literals using (#_)
open import Data.Nat using (ℕ; _≤_; zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Rational as ℚ using (ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Properties as ℚ
open import Data.Product using (_×_; proj₁; proj₂; _,_; Σ-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (true; false; not; _∨_; _∧_) renaming (Bool to 𝔹)
open import Data.Bool.Properties using (not-involutive)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

{- TODO:

   parameterised by the representation of boolean constraints

   possibly get rid of the 'query' part? unless we can combine them
   using 'and' and 'or' to get suites of properties to prove.

   include uninterpreted functions? these will have to be translated
   to separate constraints as well.
-}


data Linearity : Set where
  const linear : Linearity

data BoolKind : Set where
  constraint universal existential query : BoolKind

data QueryKind : Set where
  universal existential : QueryKind

queryKind : QueryKind → BoolKind
queryKind universal   = universal
queryKind existential = existential

data Type : Set where
  Bool   : BoolKind → Type
  Num    : Linearity → Type
  _⇒_   : Type → Type → Type
{- TODO:
  Array  : ℕ → Type → Type
  Index  : ℕ → Type
-}

data Context : Set where
  ε    : Context
  _,-_ : Context → Type → Context

data _∋_ : Context → Type → Set where
  zero : ∀ {Γ A}   →         (Γ ,- A) ∋ A
  succ : ∀ {Γ A B} → Γ ∋ A → (Γ ,- B) ∋ A

data _⊢_ : Context → Type → Set where
  -- Variables
  var    : ∀ {Γ A} → Γ ∋ A → Γ ⊢ A

  -- Functions
  ƛ      : ∀ {Γ A B} → (Γ ,- A) ⊢ B → Γ ⊢ (A ⇒ B)
  _∙_    : ∀ {Γ A B} → Γ ⊢ (A ⇒ B) → Γ ⊢ A → Γ ⊢ B

  -- Arithmetic; FIXME: could try to use instance arguments for the
  -- linearity constraints?
  const  : ∀ {Γ} → ℚ → Γ ⊢ Num const
  lift   : ∀ {Γ} → Γ ⊢ Num const → Γ ⊢ Num linear
  _`+_   : ∀ {Γ} → Γ ⊢ Num linear → Γ ⊢ Num linear → Γ ⊢ Num linear
  _`*_   : ∀ {Γ} → Γ ⊢ Num const → Γ ⊢ Num linear → Γ ⊢ Num linear

  -- Comparisons
  _`≤_   : ∀ {Γ} → Γ ⊢ Num linear → Γ ⊢ Num linear → Γ ⊢ Bool constraint

  -- Logic
  `¬_     : ∀ {Γ} → Γ ⊢ Bool constraint → Γ ⊢ Bool constraint
  _`∧_    : ∀ {Γ} → Γ ⊢ Bool constraint → Γ ⊢ Bool constraint → Γ ⊢ Bool constraint
  _`∨_    : ∀ {Γ} → Γ ⊢ Bool constraint → Γ ⊢ Bool constraint → Γ ⊢ Bool constraint

  universal   : ∀ {Γ} → Γ ⊢ Bool constraint → Γ ⊢ Bool universal
  existential : ∀ {Γ} → Γ ⊢ Bool constraint → Γ ⊢ Bool existential

  forAll  : ∀ {Γ} → (Γ ,- Num linear) ⊢ Bool universal   → Γ ⊢ Bool universal
  exists  : ∀ {Γ} → (Γ ,- Num linear) ⊢ Bool existential → Γ ⊢ Bool existential
  query   : ∀ {Γ} → (k : QueryKind) → Γ ⊢ Bool (queryKind k) → Γ ⊢ Bool query

  -- TODO: if-then-else; probably handle this the same as it is done
  -- in Idealised Algol? by endowing every type with an if-then-else
  -- algebra?

  -- TODO: network expressions; handle this by having a special
  -- function that can be used, which gets normalised to an additional
  -- constraint for every set of arguments??

------------------------------------------------------------------------------
-- proofs and refutations
ofBool : 𝔹 → Set × Set
ofBool true  = ⊤ , ⊥
ofBool false = ⊥ , ⊤

∀c : ∀ {A} → (A → Set × Set) → Set × Set
∀c ϕ = (∀ a → ϕ a .proj₁) , (Σ[ a ∈ _ ] ϕ a .proj₂)

∃c : ∀ {A} → (A → Set × Set) → Set × Set
∃c ϕ = (Σ[ a ∈ _ ] ϕ a .proj₁) , (∀ a → ϕ a .proj₂)

¬c : Set × Set → Set × Set
¬c ϕ .proj₁ = ϕ .proj₂
¬c ϕ .proj₂ = ϕ .proj₁

data Decidable (C : Set × Set) : Set where
  proof  : C .proj₁ → Decidable C
  refute : C .proj₂ → Decidable C

{-
chu : Set × Set → Set
chu C = C .proj₁ → C .proj₂ → ⊥

is-neg : ∀ {C} → Decidable C → chu C → (C .proj₁ → ⊥) → C .proj₂
is-neg (proof x) y r = ⊥-elim (r x)
is-neg (refute x) y r = x

is-neg' : ∀ {C} → Decidable C → chu C → C .proj₂ → C .proj₁ → ⊥
is-neg' x y p q = y q p

-- not an isomorphism, but they are equivalent as propositions
-}

module semantics where

  -- this module defines the “standard” semantics for the constraint
  -- language. A property is interpreted as a set of proofs and a set
  -- of refutations.

  ⟦_⟧ty : Type → Set₁
  ⟦ Bool constraint ⟧ty  = Lift _ 𝔹
  ⟦ Bool universal ⟧ty   = Set × Set
  ⟦ Bool existential ⟧ty = Set × Set
  ⟦ Bool query ⟧ty       = Set × Set
  ⟦ Num x ⟧ty            = Lift _ ℚ
  ⟦ A ⇒ B ⟧ty           = ⟦ A ⟧ty → ⟦ B ⟧ty

  ⟦_⟧ctxt : Context → Set₁
  ⟦ ε ⟧ctxt      = Lift _ ⊤
  ⟦ Γ ,- A ⟧ctxt = ⟦ Γ ⟧ctxt × ⟦ A ⟧ty

  ⟦_⟧var : ∀ {Γ A} → Γ ∋ A → ⟦ Γ ⟧ctxt → ⟦ A ⟧ty
  ⟦ zero ⟧var   (_ , a) = a
  ⟦ succ x ⟧var (γ , _) = ⟦ x ⟧var γ

  ⟦_⟧tm : ∀ {Γ A} → Γ ⊢ A → ⟦ Γ ⟧ctxt → ⟦ A ⟧ty
  ⟦ var x ⟧tm    γ = ⟦ x ⟧var γ
  ⟦ ƛ t ⟧tm      γ = λ a → ⟦ t ⟧tm (γ , a)
  ⟦ s ∙ t ⟧tm    γ = ⟦ s ⟧tm γ (⟦ t ⟧tm γ)
  ⟦ const x ⟧tm  γ = lift x
  ⟦ lift t ⟧tm   γ = ⟦ t ⟧tm γ
  ⟦ s `+ t ⟧tm   γ = lift (⟦ s ⟧tm γ .lower + ⟦ t ⟧tm γ .lower)
  ⟦ s `* t ⟧tm   γ = lift (⟦ s ⟧tm γ .lower * ⟦ t ⟧tm γ .lower)
  ⟦ s `≤ t ⟧tm   γ = lift (⟦ s ⟧tm γ .lower ℚ.≤ᵇ ⟦ t ⟧tm γ .lower)
  ⟦ `¬ t ⟧tm     γ = lift (not (⟦ t ⟧tm γ .lower))
  ⟦ s `∧ t ⟧tm   γ = lift (⟦ s ⟧tm γ .lower ∧ ⟦ t ⟧tm γ .lower)
  ⟦ s `∨ t ⟧tm   γ = lift (⟦ s ⟧tm γ .lower ∨ ⟦ t ⟧tm γ .lower)
  ⟦ universal t ⟧tm         γ = ofBool (⟦ t ⟧tm γ .lower)
  ⟦ existential t ⟧tm       γ = ofBool (⟦ t ⟧tm γ .lower)
  ⟦ forAll t ⟧tm            γ = ∀c λ x → ⟦ t ⟧tm (γ , lift x)
  ⟦ exists t ⟧tm            γ = ∃c λ x → ⟦ t ⟧tm (γ , lift x)
  ⟦ query universal t ⟧tm   γ = ⟦ t ⟧tm γ
  ⟦ query existential t ⟧tm γ = ⟦ t ⟧tm γ

------------------------------------------------------------------------------
-- Linear expressions in Δ-many variables
data LinVarCtxt : Set where
  ε   : LinVarCtxt
  _,∙ : LinVarCtxt → LinVarCtxt

data Var : LinVarCtxt → Set where
  zero : ∀ {Δ} → Var (Δ ,∙)
  succ : ∀ {Δ} → Var Δ → Var (Δ ,∙)

-- renamings
_⇒ᵣ_ : LinVarCtxt → LinVarCtxt → Set
Δ₁ ⇒ᵣ Δ₂ = Var Δ₂ → Var Δ₁

Env : LinVarCtxt → Set
Env Δ = Var Δ → ℚ

under : ∀ {Δ Δ'} → Δ ⇒ᵣ Δ' → (Δ ,∙) ⇒ᵣ (Δ' ,∙)
under ρ zero     = zero
under ρ (succ x) = succ (ρ x)

ext : ∀ {Δ} → Env Δ → ℚ → Env (Δ ,∙)
ext η q zero     = q
ext η q (succ x) = η x

data LinExp (Δ : LinVarCtxt) : Set where
  const : ℚ → LinExp Δ
  var   : ℚ → Var Δ → LinExp Δ
  _`+_  : LinExp Δ → LinExp Δ → LinExp Δ

evalLinExp : ∀ {Δ} → LinExp Δ → Env Δ → ℚ
evalLinExp (const q)  η = q
evalLinExp (var q x)  η = q * η x
evalLinExp (e₁ `+ e₂) η = evalLinExp e₁ η + evalLinExp e₂ η
{-
-- Representation as an (affine) vector
data LinExp' : LinVarCtxt → Set where
  const : ℚ → LinExp' ε
  _,-_  : ∀ {Δ} → LinExp' Δ → ℚ → LinExp' (Δ ,∙)
-- FIXME: scaling and addition are now done pointwise; we are really
-- storing them as vectors in Δ+1 dimensions (using the embedding of
-- affine space into a vector space with an extra
-- dimension). Renaming will be permutation

-- Possibly the easiest representation
record LinExp'' (Δ : LinVarCtxt) : Set where
  field
    constant : ℚ
    weights  : Var Δ → ℚ
-}

rename-LinExp : ∀ {Δ Δ'} → Δ ⇒ᵣ Δ' → LinExp Δ' → LinExp Δ
rename-LinExp ρ (const q)  = const q
rename-LinExp ρ (var q x)  = var q (ρ x)
rename-LinExp ρ (e₁ `+ e₂) = rename-LinExp ρ e₁ `+ rename-LinExp ρ e₂

rename-evalLinExp : ∀ {Δ Δ' η η'} (e : LinExp Δ') {ρ : Δ ⇒ᵣ Δ'} → (∀ x → η' (ρ x) ≡ η x) → evalLinExp e η ≡ evalLinExp (rename-LinExp ρ e) η'
rename-evalLinExp (const q)  σ = refl
rename-evalLinExp (var q x)  σ = Eq.cong (λ □ → q * □) (Eq.sym (σ x))
rename-evalLinExp (e₁ `+ e₂) σ = Eq.cong₂ _+_ (rename-evalLinExp e₁ σ) (rename-evalLinExp e₂ σ)

_⊛_ : ∀ {Δ} → ℚ → LinExp Δ → LinExp Δ
q ⊛ const x    = const (q ℚ.* x)
q ⊛ var r v    = var (q ℚ.* r) v
q ⊛ (e₁ `+ e₂) = (q ⊛ e₁) `+ (q ⊛ e₂)

eval-⊛ : ∀ {Δ} (η : Env Δ) q e → q * evalLinExp e η ≡ evalLinExp (q ⊛ e) η
eval-⊛ η q (const r) = refl
eval-⊛ η q (var r x) = Eq.sym (*-assoc q r (η x ))
eval-⊛ η q (e₁ `+ e₂) =
  begin
    q * (evalLinExp e₁ η + evalLinExp e₂ η)
  ≡⟨ *-distribˡ-+ q (evalLinExp e₁ η) (evalLinExp e₂ η) ⟩
    q * evalLinExp e₁ η + q * evalLinExp e₂ η
  ≡⟨ Eq.cong₂ _+_ (eval-⊛ η q e₁) (eval-⊛ η q e₂) ⟩
    evalLinExp (q ⊛ e₁) η + evalLinExp (q ⊛ e₂) η
  ∎
  where open Eq.≡-Reasoning

module constraints where
  -- Constraints in Negation Normal Form, as an example

  data ConstraintExp (Δ : LinVarCtxt) : Set where
    _`≤`_ : LinExp Δ → LinExp Δ → ConstraintExp Δ
    _`>`_ : LinExp Δ → LinExp Δ → ConstraintExp Δ
    _and_ : ConstraintExp Δ → ConstraintExp Δ → ConstraintExp Δ
    _or_  : ConstraintExp Δ → ConstraintExp Δ → ConstraintExp Δ

  evalConstraint : ∀ {Δ} → ConstraintExp Δ → Env Δ → 𝔹
  evalConstraint (e₁ `≤` e₂) η = evalLinExp e₁ η ℚ.≤ᵇ evalLinExp e₂ η
  evalConstraint (e₁ `>` e₂) η = not (evalLinExp e₁ η ℚ.≤ᵇ evalLinExp e₂ η)
  evalConstraint (p and q)   η = evalConstraint p η ∧ evalConstraint q η
  evalConstraint (p or q)    η = evalConstraint p η ∨ evalConstraint q η

  negate : ∀ {Δ} → ConstraintExp Δ → ConstraintExp Δ
  negate (e₁ `≤` e₂) = e₁ `>` e₂
  negate (e₁ `>` e₂) = e₁ `≤` e₂
  negate (p and q)   = (negate p) or (negate q)
  negate (p or q)    = (negate p) and (negate q)

  not-and : ∀ {x y} → not (x ∧ y) ≡ not x ∨ not y
  not-and {false} {y} = refl
  not-and {true} {y} = refl

  not-or : ∀ {x y} → not (x ∨ y) ≡ not x ∧ not y
  not-or {false} = refl
  not-or {true} = refl

  eval-negate : ∀ {Δ} (η : Env Δ) e → not (evalConstraint e η) ≡ evalConstraint (negate e) η
  eval-negate η (e₁ `≤` e₂) = refl
  eval-negate η (e₁ `>` e₂) = not-involutive _
  eval-negate η (p and q)   rewrite not-and {evalConstraint p η}{evalConstraint q η}
                            rewrite eval-negate η p
                            rewrite eval-negate η q = refl
  eval-negate η (p or q)    rewrite not-or {evalConstraint p η}{evalConstraint q η}
                            rewrite eval-negate η p
                            rewrite eval-negate η q = refl

  rename-ConstraintExp : ∀ {Δ Δ'} → Δ ⇒ᵣ Δ' → ConstraintExp Δ' → ConstraintExp Δ
  rename-ConstraintExp ρ (e₁ `≤` e₂) = (rename-LinExp ρ e₁) `≤` (rename-LinExp ρ e₂)
  rename-ConstraintExp ρ (e₁ `>` e₂) = (rename-LinExp ρ e₁) `>` (rename-LinExp ρ e₂)
  rename-ConstraintExp ρ (p and q)   = (rename-ConstraintExp ρ p) and (rename-ConstraintExp ρ q)
  rename-ConstraintExp ρ (p or q)    = (rename-ConstraintExp ρ p) or (rename-ConstraintExp ρ q)

  eval-rename : ∀ {Δ} c (η : Env Δ) {Δ'} (ρ : Δ' ⇒ᵣ Δ) (η' : Env Δ') → (∀ x → η' (ρ x) ≡ η x) →
                evalConstraint c η ≡ evalConstraint (rename-ConstraintExp ρ c) η'
  eval-rename (e₁ `≤` e₂) η ρ η' σ = Eq.cong₂ ℚ._≤ᵇ_ (rename-evalLinExp e₁ σ) (rename-evalLinExp e₂ σ)
  eval-rename (e₁ `>` e₂) η ρ η' σ = Eq.cong not (Eq.cong₂ ℚ._≤ᵇ_ (rename-evalLinExp e₁ σ) (rename-evalLinExp e₂ σ))
  eval-rename (p and q) η ρ η' σ = Eq.cong₂ _∧_ (eval-rename p η ρ η' σ) (eval-rename q η ρ η' σ)
  eval-rename (p or q) η ρ η' σ = Eq.cong₂ _∨_ (eval-rename p η ρ η' σ) (eval-rename q η ρ η' σ)

  -- Then, a query is an existential statement for a collection of
  -- variables over a constraint expression; interpreted either as a
  -- counterexample or a witness.

  data Query : LinVarCtxt → Set where
    constr   : ∀ {Δ} → ConstraintExp Δ → Query Δ
    quantify : ∀ {Δ} → Query (Δ ,∙) → Query Δ

  evalQuery : ∀ {Δ} → Query Δ → Env Δ → Set × Set
  evalQuery (constr p)   η = ofBool (evalConstraint p η)
  evalQuery (quantify q) η = ∃c (λ r → evalQuery q (ext η r))

  rename-Query : ∀ {Δ Δ'} → Δ ⇒ᵣ Δ' → Query Δ' → Query Δ
  rename-Query ρ (constr c)    = constr (rename-ConstraintExp ρ c)
  rename-Query ρ (quantify qu) = quantify (rename-Query (under ρ) qu)

  data Property (Δ : LinVarCtxt) : Set where
     refute  : Query Δ → Property Δ
     witness : Query Δ → Property Δ

  rename-Property : ∀ {Δ Δ'} → Δ ⇒ᵣ Δ' → Property Δ' → Property Δ
  rename-Property ρ (refute q)  = refute (rename-Query ρ q)
  rename-Property ρ (witness q) = witness (rename-Query ρ q)

  evalProperty : ∀ {Δ} → Property Δ → Env Δ → Set × Set
  evalProperty (refute q)  η = ¬c (evalQuery q η)
  evalProperty (witness q) η = evalQuery q η

module nbe where

  open constraints

  -- Semi-syntactically interpreted types
  ⟦_⟧ty : Type → LinVarCtxt → Set
  ⟦ Bool constraint ⟧ty  Δ = ConstraintExp Δ
  ⟦ Bool universal ⟧ty   Δ = Query Δ
  ⟦ Bool existential ⟧ty Δ = Query Δ
  ⟦ Bool query ⟧ty       Δ = Property Δ
  ⟦ Num const ⟧ty        Δ = ℚ
  ⟦ Num linear ⟧ty       Δ = LinExp Δ
  ⟦ A ⇒ B ⟧ty           Δ = ∀ Δ' → Δ' ⇒ᵣ Δ → ⟦ A ⟧ty Δ' → ⟦ B ⟧ty Δ'

  rename-ty : ∀ {A Δ Δ'} → Δ ⇒ᵣ Δ' → ⟦ A ⟧ty Δ' → ⟦ A ⟧ty Δ
  rename-ty {Bool constraint}  ρ a = rename-ConstraintExp ρ a
  rename-ty {Bool universal}   ρ a = rename-Query ρ a
  rename-ty {Bool existential} ρ a = rename-Query ρ a
  rename-ty {Bool query}       ρ a = rename-Property ρ a
  rename-ty {Num const}        ρ q = q
  rename-ty {Num linear}       ρ e = rename-LinExp ρ e
  rename-ty {A ⇒ B}           ρ f = λ Δ'' ρ' → f Δ'' (λ x → ρ' (ρ x))

  ⟦_⟧ctxt : Context → LinVarCtxt → Set
  ⟦ ε ⟧ctxt      Δ = ⊤
  ⟦ Γ ,- A ⟧ctxt Δ = ⟦ Γ ⟧ctxt Δ × ⟦ A ⟧ty Δ

  rename-ctxt : ∀ {Γ Δ Δ'} → Δ ⇒ᵣ Δ' → ⟦ Γ ⟧ctxt Δ' → ⟦ Γ ⟧ctxt Δ
  rename-ctxt {ε}      ρ tt      = tt
  rename-ctxt {Γ ,- A} ρ (γ , a) = rename-ctxt ρ γ , rename-ty ρ a

  ⟦_⟧var : ∀ {Γ A} → Γ ∋ A → ∀ {Δ} → ⟦ Γ ⟧ctxt Δ → ⟦ A ⟧ty Δ
  ⟦ zero ⟧var   (_ , a) = a
  ⟦ succ x ⟧var (γ , _) = ⟦ x ⟧var γ

  ⟦_⟧tm : ∀ {Γ A} → Γ ⊢ A → ∀ {Δ} → ⟦ Γ ⟧ctxt Δ → ⟦ A ⟧ty Δ
  ⟦ var x ⟧tm    γ = ⟦ x ⟧var γ
  ⟦ ƛ t ⟧tm      γ = λ Δ' ρ a → ⟦ t ⟧tm (rename-ctxt ρ γ , a)
  ⟦ s ∙ t ⟧tm    γ = ⟦ s ⟧tm γ _ (λ x → x) (⟦ t ⟧tm γ)
  ⟦ const x ⟧tm  γ = x
  ⟦ lift t ⟧tm   γ = const (⟦ t ⟧tm γ)
  ⟦ s `+ t ⟧tm   γ = ⟦ s ⟧tm γ `+ ⟦ t ⟧tm γ
  ⟦ s `* t ⟧tm   γ = ⟦ s ⟧tm γ ⊛ ⟦ t ⟧tm γ
  ⟦ s `≤ t ⟧tm   γ = ⟦ s ⟧tm γ `≤` ⟦ t ⟧tm γ
  ⟦ `¬ t ⟧tm     γ = negate (⟦ t ⟧tm γ)
  ⟦ s `∧ t ⟧tm   γ = (⟦ s ⟧tm γ) and (⟦ t ⟧tm γ)
  ⟦ s `∨ t ⟧tm   γ = (⟦ s ⟧tm γ) or (⟦ t ⟧tm γ)
  ⟦ universal t ⟧tm γ = constr (negate (⟦ t ⟧tm γ))
  ⟦ existential t ⟧tm γ = constr (⟦ t ⟧tm γ)
  ⟦ forAll t ⟧tm γ = quantify (⟦ t ⟧tm (rename-ctxt succ γ , var 1ℚ zero))
  ⟦ exists t ⟧tm γ = quantify (⟦ t ⟧tm (rename-ctxt succ γ , var 1ℚ zero))
  ⟦ query universal t ⟧tm   γ = refute (⟦ t ⟧tm γ)
  ⟦ query existential t ⟧tm γ = witness (⟦ t ⟧tm γ)

  normalise : ε ⊢ Bool query → Property ε
  normalise t = ⟦ t ⟧tm tt
{-
  _ : Property ε
  _ = {!normalise (query universal (forAll (forAll (universal ((var (succ (zero))) `≤ (var zero))))))!}
-}

record _≅_ (A B : Set) : Set where
  field
    fwd : A → B
    bwd : B → A
    fwd∘bwd : ∀ b → fwd (bwd b) ≡ b
    bwd∘fwd : ∀ a → bwd (fwd a) ≡ a
open _≅_

record _≅c_ (A B : Set × Set) : Set where
  field
    proof-iso  : A .proj₁ ≅ B .proj₁
    refute-iso : A .proj₂ ≅ B .proj₂
open _≅c_

postulate
  -- FIXME: use setoids?
  fext : ∀ {A : Set}{B : A → Set} → {f g : ∀ a → B a} → (∀ a → f a ≡ g a) → f ≡ g

∃c-≅ : ∀ {X : Set} {A B : X → Set × Set} → (∀ x → A x ≅c B x) → ∃c A ≅c ∃c B
∃c-≅ A≅B .proof-iso .fwd (x , a) = x , A≅B x .proof-iso .fwd a
∃c-≅ A≅B .proof-iso .bwd (x , b) = x , A≅B x .proof-iso .bwd b
∃c-≅ A≅B .proof-iso .fwd∘bwd (x , b) = Eq.cong (λ □ → (x , □)) (A≅B x .proof-iso .fwd∘bwd b)
∃c-≅ A≅B .proof-iso .bwd∘fwd (x , a) = Eq.cong (λ □ → (x , □)) (A≅B x .proof-iso .bwd∘fwd a)
∃c-≅ A≅B .refute-iso .fwd f x = A≅B x .refute-iso .fwd (f x)
∃c-≅ A≅B .refute-iso .bwd f x = A≅B x .refute-iso .bwd (f x)
∃c-≅ A≅B .refute-iso .fwd∘bwd f = fext (λ a → A≅B a .refute-iso .fwd∘bwd (f a))
∃c-≅ A≅B .refute-iso .bwd∘fwd f = fext (λ a → A≅B a .refute-iso .bwd∘fwd (f a))

module logical-rel where

  -- Logical relation to show that the normalised version matches the
  -- semantics of the original version.

  -- “worlds” are now pairs of LinVarContexts and Environments; world
  -- extension is a value-preserving renaming.

  open constraints using (evalConstraint; negate; evalQuery; evalProperty)

  ⟦_⟧ty : (A : Type) → ∀ {Δ} → Env Δ → semantics.⟦ A ⟧ty → nbe.⟦ A ⟧ty Δ → Set₁
  ⟦ Bool constraint ⟧ty  η x  y  = Lift _ (x .lower ≡ evalConstraint y η)
  ⟦ Bool universal ⟧ty   η x  y  = Lift _ (x ≅c ¬c (evalQuery y η))
  ⟦ Bool existential ⟧ty η x  y  = Lift _ (x ≅c evalQuery y η)
  ⟦ Bool query ⟧ty       η x  y  = Lift _ (x ≅c evalProperty y η)
  ⟦ Num const ⟧ty        η q  r  = Lift _ (q .lower ≡ r)
  ⟦ Num linear ⟧ty       η q  e  = Lift _ (q .lower ≡ evalLinExp e η)
  ⟦ A ⇒ B ⟧ty            η f₁ f₂ = ∀ {Δ'} η' ρ → (∀ x → η' (ρ x) ≡ η x) → ∀ {x₁ x₂} → ⟦ A ⟧ty η' x₁ x₂ → ⟦ B ⟧ty η' (f₁ x₁) (f₂ Δ' ρ x₂)

  extend-ty : ∀ {A Δ Δ' η η'} → (ρ : Δ ⇒ᵣ Δ') → (∀ x → η' (ρ x) ≡ η x) → ∀ {a₁ a₂} → ⟦ A ⟧ty η a₁ a₂ → ⟦ A ⟧ty η' a₁ (nbe.rename-ty ρ a₂)
  extend-ty {Bool constraint}  ρ σ {a₂ = c} (lift refl) =
     lift (constraints.eval-rename c _ ρ _ σ)
  extend-ty {Bool universal}   ρ σ {a₁}{a₂ = p} (lift eq) = lift {!!}
  extend-ty {Bool existential} ρ σ (lift eq) = lift {!!}
  extend-ty {Bool query} ρ σ (lift eq) = lift {!!}
  extend-ty {Num const}  ρ σ a₁-a₂ = a₁-a₂
  extend-ty {Num linear} ρ σ {_}{e} (lift refl) = lift (rename-evalLinExp e σ)
  extend-ty {A ⇒ B}      ρ σ f₁-f₂ = λ η' ρ' σ' → f₁-f₂ η' (λ x → ρ' (ρ x)) (λ x → Eq.trans (σ' (ρ x)) (σ x))

  ⟦_⟧ctxt : (Γ : Context) → ∀ {Δ} → Env Δ → semantics.⟦ Γ ⟧ctxt → nbe.⟦ Γ ⟧ctxt Δ → Set₁
  ⟦ ε ⟧ctxt      η (lift tt) tt        = Lift _ ⊤
  ⟦ Γ ,- A ⟧ctxt η (γ₁ , a₁) (γ₂ , a₂) = ⟦ Γ ⟧ctxt η γ₁ γ₂ × ⟦ A ⟧ty η a₁ a₂

  extend-ctxt : ∀ {Γ Δ Δ' η η'} → (ρ : Δ ⇒ᵣ Δ') → (∀ x → η' (ρ x) ≡ η x) → ∀ {γ₁ γ₂} → ⟦ Γ ⟧ctxt η γ₁ γ₂ → ⟦ Γ ⟧ctxt η' γ₁ (nbe.rename-ctxt ρ γ₂)
  extend-ctxt {ε}      ρ σ (lift tt)       = lift tt
  extend-ctxt {Γ ,- A} ρ σ (γ₁-γ₂ , a₁-a₂) = extend-ctxt {Γ} ρ σ γ₁-γ₂ , extend-ty {A} ρ σ a₁-a₂

  -- All variables' interpretations are related
  ⟦_⟧var : ∀ {Γ A} (x : Γ ∋ A) {Δ} (η : Env Δ) {γ₁ γ₂} → ⟦ Γ ⟧ctxt η γ₁ γ₂ → ⟦ A ⟧ty η (semantics.⟦ x ⟧var γ₁) (nbe.⟦ x ⟧var γ₂)
  ⟦ zero ⟧var   η (_ , a₁-a₂) = a₁-a₂
  ⟦ succ x ⟧var η (γ₁-γ₂ , _) = ⟦ x ⟧var η γ₁-γ₂

  -- All terms' interpretations are related
  ⟦_⟧tm : ∀ {Γ A} (t : Γ ⊢ A) {Δ} (η : Env Δ) {γ₁ γ₂} → ⟦ Γ ⟧ctxt η γ₁ γ₂ → ⟦ A ⟧ty η (semantics.⟦ t ⟧tm γ₁) (nbe.⟦ t ⟧tm γ₂)
  ⟦ var x ⟧tm η γ₁-γ₂ = ⟦ x ⟧var η γ₁-γ₂
  ⟦ ƛ t ⟧tm η γ₁-γ₂ = λ η' ρ η'-ρ a₁-a₂ → ⟦ t ⟧tm η' (extend-ctxt ρ η'-ρ γ₁-γ₂ , a₁-a₂)
  ⟦ s ∙ t ⟧tm η γ₁-γ₂ =
    ⟦ s ⟧tm η γ₁-γ₂ η (λ x → x) (λ x → refl) (⟦ t ⟧tm η γ₁-γ₂)
  ⟦ const x ⟧tm η γ₁-γ₂ .lower = refl
  ⟦ lift t ⟧tm η γ₁-γ₂ = ⟦ t ⟧tm η γ₁-γ₂
  ⟦ s `+ t ⟧tm η {γ₁}{γ₂} γ₁-γ₂ .lower =
    begin
        semantics.⟦ s ⟧tm γ₁ .lower + semantics.⟦ t ⟧tm γ₁ .lower
    ≡⟨ Eq.cong₂ _+_ (⟦ s ⟧tm η γ₁-γ₂ .lower) (⟦ t ⟧tm η γ₁-γ₂ .lower) ⟩
        evalLinExp (nbe.⟦ s ⟧tm γ₂) η + evalLinExp (nbe.⟦ t ⟧tm γ₂) η
    ∎
    where open Eq.≡-Reasoning
  ⟦ s `* t ⟧tm η {γ₁}{γ₂} γ₁-γ₂ .lower =
    begin
         semantics.⟦ s ⟧tm γ₁ .lower * semantics.⟦ t ⟧tm γ₁ .lower
    ≡⟨ Eq.cong₂ _*_ (⟦ s ⟧tm η γ₁-γ₂ .lower) (⟦ t ⟧tm η γ₁-γ₂ .lower) ⟩
         nbe.⟦ s ⟧tm γ₂ * evalLinExp (nbe.⟦ t ⟧tm γ₂) η
    ≡⟨ eval-⊛ η (nbe.⟦ s ⟧tm γ₂) (nbe.⟦ t ⟧tm γ₂) ⟩
         evalLinExp (nbe.⟦ s ⟧tm γ₂ ⊛ nbe.⟦ t ⟧tm γ₂) η
    ∎
    where open Eq.≡-Reasoning
  ⟦ s `≤ t ⟧tm η {γ₁}{γ₂} γ₁-γ₂ .lower =
    begin
      semantics.⟦ s ⟧tm γ₁ .lower ℚ.≤ᵇ semantics.⟦ t ⟧tm γ₁ .lower
    ≡⟨ Eq.cong₂ ℚ._≤ᵇ_ (⟦ s ⟧tm η γ₁-γ₂ .lower) (⟦ t ⟧tm η γ₁-γ₂ .lower) ⟩
      evalLinExp (nbe.⟦ s ⟧tm γ₂) η ℚ.≤ᵇ evalLinExp (nbe.⟦ t ⟧tm γ₂) η
    ∎
    where open Eq.≡-Reasoning
  ⟦ `¬ t ⟧tm η {γ₁}{γ₂} γ₁-γ₂ .lower =
    begin
      not (semantics.⟦ t ⟧tm γ₁ .lower)
    ≡⟨ Eq.cong not (⟦ t ⟧tm η γ₁-γ₂ .lower) ⟩
      not (evalConstraint (nbe.⟦ t ⟧tm γ₂) η)
    ≡⟨ constraints.eval-negate η (nbe.⟦ t ⟧tm γ₂) ⟩
      evalConstraint (negate (nbe.⟦ t ⟧tm γ₂)) η
    ∎
    where open Eq.≡-Reasoning
  ⟦ s `∧ t ⟧tm η {γ₁}{γ₂} γ₁-γ₂ .lower =
    begin
      semantics.⟦ s ⟧tm γ₁ .lower       ∧ semantics.⟦ t ⟧tm γ₁ .lower
    ≡⟨ Eq.cong₂ _∧_ (⟦ s ⟧tm η γ₁-γ₂ .lower) (⟦ t ⟧tm η γ₁-γ₂ .lower) ⟩
      evalConstraint (nbe.⟦ s ⟧tm γ₂) η ∧ evalConstraint (nbe.⟦ t ⟧tm γ₂) η
    ∎
    where open Eq.≡-Reasoning
  ⟦ s `∨ t ⟧tm η {γ₁}{γ₂} γ₁-γ₂ .lower =
    begin
      semantics.⟦ s ⟧tm γ₁ .lower       ∨ semantics.⟦ t ⟧tm γ₁ .lower
    ≡⟨ Eq.cong₂ _∨_ (⟦ s ⟧tm η γ₁-γ₂ .lower) (⟦ t ⟧tm η γ₁-γ₂ .lower) ⟩
      evalConstraint (nbe.⟦ s ⟧tm γ₂) η ∨ evalConstraint (nbe.⟦ t ⟧tm γ₂) η
    ∎
    where open Eq.≡-Reasoning
  ⟦ universal t ⟧tm η γ₁-γ₂ .lower = {!!} -- FIXME: stuff to do with negation
  ⟦ existential t ⟧tm η γ₁-γ₂ .lower rewrite ⟦ t ⟧tm η γ₁-γ₂ .lower = {!!} -- FIXME: reflexive isos
  ⟦ forAll t ⟧tm η γ₁-γ₂ .lower = {!!} -- FIXME: ¬∃ ≅ ∀¬
  ⟦ exists t ⟧tm η γ₁-γ₂ .lower =
    -- FIXME: extending related contexts with a variable
    ∃c-≅ (λ q → ⟦ t ⟧tm (ext η q) ({!!} , lift (Eq.sym (ℚ.*-identityˡ q))) .lower)
  ⟦ query universal t ⟧tm η γ₁-γ₂ = ⟦ t ⟧tm η γ₁-γ₂
  ⟦ query existential t ⟧tm η γ₁-γ₂ = ⟦ t ⟧tm η γ₁-γ₂

  -- Overall theorem: a closed property normalises to a syntactic form
  -- with an isomorphic solution set.

  thm : ∀ (t : ε ⊢ Bool query) → semantics.⟦ t ⟧tm (lift tt) ≅c evalProperty (nbe.normalise t) (λ ())
  thm t = ⟦ t ⟧tm (λ ()) (lift tt) .lower

-- Problems and problem reductions, expressed as containers
record Problem : Set₁ where
  field
    problem  : Set
    solution : problem → Set
open Problem

record _==>_ (P Q : Problem) : Set where
  field
    reduce    : P .problem → Q .problem
    translate : (p : P .problem) → Q .solution (reduce p) → P .solution p
    -- Or do we want containers over Chu? This wouldn't give us
    -- decidability! Might be interesting though.
open _==>_

-- or do we want cartesian morphisms?

I : Problem
I .problem = ⊤
I .solution tt = ⊤

constraintProblem : Problem
constraintProblem .problem = ε ⊢ Bool query
constraintProblem .solution t = Decidable (semantics.⟦ t ⟧tm (lift tt))

solverProblem : Problem
solverProblem .problem    = constraints.Property ε
solverProblem .solution p = Decidable (constraints.evalProperty p (λ ()))

-- this seems to need a Chu-information morphism to work! Also, only
-- need a small part of what we proved.
nrml : constraintProblem ==> solverProblem
nrml .reduce = nbe.normalise
nrml .translate p (proof x)  = proof (logical-rel.thm p .proof-iso .bwd x)
nrml .translate p (refute x) = refute (logical-rel.thm p .refute-iso .bwd x)

{-
solver : solverProblem ==> I
solver .reduce    _ = tt
solver .translate p tt = {!!}
-}

{- A query is something of the form ∃x₁, ..., xₙ. C(x₁, ..., xₙ)

   A solution is one of:
   - a witness (answers to x₁, ..., xₙ)
   - a proof that ∀ x₁ ... xₙ . ¬C(x₁, ..., xₙ)

   How we interpret this is up to the caller.

   FIXME: given a pure “solver” turn it into a witness-finder /
   refuter. Can this be done via another problem reduction? -}


-- - For Marabou: convert to DNF and extract the uninterpreted network
--   function as an additional constraint. Then apply F-M elimination
--   to get into Marabou form. Ultimately, we get a nested list of
--   disjunctive constraints.

-- Key ingredients:

-- 1. Use of proofs and refutations in the solution sets. The
--    semantics of a problem consists of what it means to prove and
--    what it means to refute it.
--
-- 2. Sometimes we don't care about the refutation; just the fact it
--    failed so we can go on to something else.
--
-- 3. If we have a collection of properties to prove, then we'll get a
--    list of queries for the solver, all of which need to be
--    solved. However, in the DNF case of Marabou, we get a
--    disjunction of problems for each property (only one of which
--    needs a proof); and a conjunction of properties.
