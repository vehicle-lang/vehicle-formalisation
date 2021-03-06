{-# OPTIONS --postfix-projections --safe #-}

module NormalisationCorrect where

open import Data.Bool using (not; _β§_; _β¨_; true; false)
                   renaming (Bool to πΉ; if_then_else_ to ifα΅_then_else_)
open import Data.Product using (_Γ_; _,_; projβ; projβ)
open import Data.Unit using (β€; tt)
open import Data.Rational using (β; _+_; _*_; _β€α΅_; _β_)
open import Data.Rational.Properties using (*-identityΛ‘)
open import Relation.Binary.PropositionalEquality using (_β‘_; refl; sym; trans; cong; congβ)
open import Relation.Nullary using (does)

open import MiniVehicle
open import NormalisedExpr
import StandardSemantics as S
import Normalisation as N

------------------------------------------------------------------------------
-- worlds are pairs of LinVarCtxts and Environments for them

record World : Set where
  constructor _,_
  field
    ctxt : LinVarCtxt
    env  : Env ctxt
open World

-- world morphisms extend the context so that the environment is
-- preserved
record _βw_ (wβ wβ : World) : Set where
  field
    ren   : wβ .ctxt βα΅£ wβ .ctxt
    presv : β x β wβ .env (ren x) β‘ wβ .env x
open _βw_

id-w : β {w} β w βw w
id-w .ren x = x
id-w .presv x = refl

_βw_ : β {wβ wβ wβ} β wβ βw wβ β wβ βw wβ β wβ βw wβ
(f βw g) .ren x = g .ren (f .ren x)
(f βw g) .presv x = trans (g .presv (f .ren x)) (f .presv x)

------------------------------------------------------------------------------

WRel : Set β (LinVarCtxt β Set) β Setβ
WRel A B = β (w : World) β A β B (w .ctxt) β Set

-- FIXME: move to NormalisationExpr
extend-env : β {Ξ} β Env Ξ β β β Env (Ξ ,β)
extend-env Ξ· q zero     = q
extend-env Ξ· q (succ x) = Ξ· x

module _ (extFunc : β β β) where

  LetLiftR : β {A B} β WRel A B β WRel A (LetLift B)
  LetLiftR R w a (return b) = R w a b
  LetLiftR R w a (if c kβ kβ) =
    ifα΅ (eval-ConstraintExp extFunc c (w .env))
     then LetLiftR R w a kβ
     else LetLiftR R w a (kβ (Ξ» x β x))
  LetLiftR R w a (let-linexp e k) =
    LetLiftR R ((w .ctxt ,β) , extend-env (w .env) (eval-LinExp e (w .env))) a k
  LetLiftR R w a (let-funexp x k) =
    LetLiftR R (((w .ctxt ,β) , extend-env (w .env) (extFunc (w .env x)))) a k

  let-bindR : β {A A' B B'}{RA : WRel A A'}{RB : WRel B B'} w x y (f : A β B) g β
    LetLiftR RA w x y β
    (β w' (Ο : w' βw w) a b β RA w' a b β LetLiftR RB w' (f a) (g (w' .ctxt) (Ο .ren) b)) β
    LetLiftR RB w (f x) (bind-let y g)
  let-bindR w x (return y) f g r-xy r-fg = r-fg w id-w x y r-xy
  let-bindR w x (if e yβ yβ) f g r-xy r-fg with eval-ConstraintExp extFunc e (w .env)
  ... | true  = let-bindR w x yβ f g r-xy r-fg
  ... | false = let-bindR w x (yβ (Ξ» x β x)) f g r-xy r-fg
  let-bindR w x (let-linexp e y) f g r-xy r-fg =
    let-bindR
      ((w .ctxt ,β) , extend-env (w .env) (eval-LinExp e (w .env)))
      x
      y
      f
      (Ξ» Ξ' Ο a' β g Ξ' (Ξ» xβ β Ο (succ xβ)) a')
      r-xy
      Ξ» w' Ο a b r-ab β
        r-fg
          w' (record { ren = Ξ» xβ β Ο .ren (succ xβ) ; presv = Ξ» xβ β Ο .presv (succ xβ) })
          a b r-ab
          -- FIXME: tidy up this 'record' bit
  let-bindR w x (let-funexp v y) f g r-xy r-fg =
    let-bindR
      ((w .ctxt ,β) , extend-env (w .env) (extFunc (w .env v)))
      x
      y
      f
      (Ξ» Ξ' Ο a' β g Ξ' (Ξ» xβ β Ο (succ xβ)) a')
      r-xy
      Ξ» w' Ο a b r-ab β
        r-fg w' (record { ren = Ξ» xβ β Ο .ren (succ xβ) ; presv = Ξ» xβ β Ο .presv (succ xβ) })
        a b r-ab


  ------------------------------------------------------------------------------
  ext-evalLinExp :
    β {wβ wβ} e (Ο : wβ βw wβ) β
      eval-LinExp e (wβ .env) β‘ eval-LinExp (rename-LinExp (Ο .ren) e) (wβ .env)
  ext-evalLinExp (const q)  Ο = refl
  ext-evalLinExp (var q x)  Ο = cong (Ξ» β‘ β q * β‘) (sym (Ο .presv x))
  ext-evalLinExp (eβ `+ eβ) Ο = congβ _+_ (ext-evalLinExp eβ Ο) (ext-evalLinExp eβ Ο)

  ext-evalConstraint :
    β {wβ wβ} p (Ο : wβ βw wβ) β
      eval-ConstraintExp extFunc p (wβ .env)
      β‘ eval-ConstraintExp extFunc (rename-ConstraintExp (Ο .ren) p) (wβ .env)
  ext-evalConstraint (eβ `β€` eβ) Ο rewrite ext-evalLinExp eβ Ο rewrite ext-evalLinExp eβ Ο = refl
  ext-evalConstraint (eβ `>` eβ) Ο rewrite ext-evalLinExp eβ Ο rewrite ext-evalLinExp eβ Ο = refl
  ext-evalConstraint (eβ `=` eβ) Ο rewrite ext-evalLinExp eβ Ο rewrite ext-evalLinExp eβ Ο = refl
  ext-evalConstraint (eβ `β ` eβ) Ο rewrite ext-evalLinExp eβ Ο rewrite ext-evalLinExp eβ Ο = refl
  ext-evalConstraint (p and q)   Ο rewrite ext-evalConstraint p Ο rewrite ext-evalConstraint q Ο = refl
  ext-evalConstraint (p or q)    Ο rewrite ext-evalConstraint p Ο rewrite ext-evalConstraint q Ο = refl
  ext-evalConstraint (x `=`f y)  Ο rewrite Ο .presv x rewrite Ο .presv y = refl
  ext-evalConstraint (x `β `f y)  Ο rewrite Ο .presv x rewrite Ο .presv y = refl

  ------------------------------------------------------------------------------
  -- Relatedness for types
  β¦_β§ty : β A β WRel S.β¦ A β§ty N.β¦ A β§ty
  β¦ Bool constraint β§ty w x y = x β‘ eval-ConstraintExp extFunc y (w .env)
  β¦ Num const β§ty       w x y = x β‘ y
  β¦ Num linear β§ty      w x y = x β‘ eval-LinExp y (w .env)
  β¦ A β B β§ty          w f g =
    β w' (Ο : w' βw w) x y β
      β¦ A β§ty w' x y β
      LetLiftR β¦ B β§ty w' (f x) (g (w' .ctxt) (Ο .ren) y)

  ext-ty : β A {wβ wβ} β (Ο : wβ βw wβ) β β {x y} β
           β¦ A β§ty wβ x y β
           β¦ A β§ty wβ x (N.rename-ty A (Ο .ren) y)
  ext-ty (Bool constraint) Ο {x}{y} r =
    trans r (ext-evalConstraint y Ο)
  ext-ty (Num const) Ο r = r
  ext-ty (Num linear) Ο {x}{y} r = trans r (ext-evalLinExp y Ο)
  ext-ty (A β B) Ο r =
    Ξ» wβ Οβ xβ yβ rβ β r wβ (Ο βw Οβ) xβ yβ rβ

  -- Relatedness for contexts
  β¦_β§ctxt : β Ξ β WRel S.β¦ Ξ β§ctxt N.β¦ Ξ β§ctxt
  β¦ Ξ΅ β§ctxt      w tt      tt       = β€
  β¦ Ξ ,- A β§ctxt w (Ξ³β , x) (Ξ³β , y) = β¦ Ξ β§ctxt w Ξ³β Ξ³β Γ β¦ A β§ty w x y

  ext-ctxt : β Ξ {wβ wβ} (Ο : wβ βw wβ) β β {x y} β
             β¦ Ξ β§ctxt wβ x y β
             β¦ Ξ β§ctxt wβ x (N.rename-ctxt (Ο .ren) y)
  ext-ctxt Ξ΅ Ο r = tt
  ext-ctxt (Ξ ,- A) Ο (Ξ³βΞ³β , aβaβ) =
    (ext-ctxt Ξ Ο Ξ³βΞ³β) , (ext-ty A Ο aβaβ)

  -- Variables' interpretations are related
  β¦_β§var : β {Ξ A} (x : Ξ β A) w {Ξ³β Ξ³β} β
          β¦ Ξ β§ctxt w Ξ³β Ξ³β β
          β¦ A β§ty w (S.β¦ x β§var Ξ³β) (N.β¦ x β§var Ξ³β)
  β¦ zero β§var   w (_    , x-y) = x-y
  β¦ succ x β§var w (Ξ³β-Ξ³β , _  ) = β¦ x β§var w Ξ³β-Ξ³β

  module ST = S.TermSem (extFunc)

  -- Terms' interpretations are related
  β¦_β§tm : β {Ξ A} (x : Ξ β’ A) w {Ξ³β Ξ³β} β
          β¦ Ξ β§ctxt w Ξ³β Ξ³β β
          LetLiftR β¦ A β§ty w (ST.β¦ x β§tm Ξ³β) (N.β¦ x β§tm Ξ³β)
  β¦ var x β§tm w Ξ³β-Ξ³β = β¦ x β§var w Ξ³β-Ξ³β
  β¦ Ζ t β§tm w Ξ³β-Ξ³β =
    Ξ» w' Ο x y x-y β β¦ t β§tm w' (ext-ctxt _ Ο Ξ³β-Ξ³β , x-y)
  β¦ s β t β§tm w {Ξ³β}{Ξ³β} Ξ³β-Ξ³β =
    let-bindR w (ST.β¦ s β§tm Ξ³β) (N.β¦ s β§tm Ξ³β)
      _ -- (Ξ» a β a (S.β¦ t β§tm Ξ³β))
      _
      (β¦ s β§tm w Ξ³β-Ξ³β)
      Ξ» w' Ο a b r-ab β
        let-bindR w' (ST.β¦ t β§tm Ξ³β) (N.β¦ t β§tm (N.rename-ctxt (Ο .ren) Ξ³β))
          _ -- (Ξ» a' β a a')
          _
          (β¦ t β§tm w' (ext-ctxt _ Ο Ξ³β-Ξ³β))
          r-ab
  β¦ func t β§tm w {Ξ³β}{Ξ³β} Ξ³β-Ξ³β =
    let-bindR w (ST.β¦ t β§tm Ξ³β) (N.β¦ t β§tm Ξ³β)
      extFunc
      _
      (β¦ t β§tm w Ξ³β-Ξ³β)
      Ξ» { w' Ο a b refl β sym (*-identityΛ‘ _) }
  β¦ const x β§tm w Ξ³β-Ξ³β = refl
  β¦ lift t β§tm w {Ξ³β}{Ξ³β} Ξ³β-Ξ³β =
    let-bindR w (ST.β¦ t β§tm Ξ³β) (N.β¦ t β§tm Ξ³β)
     (Ξ» a β a)
     (Ξ» _ _ q β return (const q))
     (β¦ t β§tm w Ξ³β-Ξ³β)
     Ξ» w' Ο a b aβ‘b β aβ‘b
  β¦ s `+ t β§tm w {Ξ³β}{Ξ³β} Ξ³β-Ξ³β =
    let-bindR w (ST.β¦ s β§tm Ξ³β) (N.β¦ s β§tm Ξ³β)
      (Ξ» a β a + ST.β¦ t β§tm Ξ³β)
      _
      (β¦ s β§tm w Ξ³β-Ξ³β)
      Ξ» w' Ο a b r-ab β
        let-bindR w' (ST.β¦ t β§tm Ξ³β) (N.β¦ t β§tm (N.rename-ctxt (Ο .ren) Ξ³β))
          (Ξ» b β a + b)
          _
          (β¦ t β§tm w' (ext-ctxt _ Ο Ξ³β-Ξ³β))
          Ξ» w'' Οβ aβ bβ r-aβbβ β
            congβ _+_ (trans r-ab (ext-evalLinExp b Οβ)) r-aβbβ
  β¦ s `* t β§tm w {Ξ³β}{Ξ³β} Ξ³β-Ξ³β =
    let-bindR w (ST.β¦ s β§tm Ξ³β) (N.β¦ s β§tm Ξ³β)
      (Ξ» a β a * ST.β¦ t β§tm Ξ³β)
      _
      (β¦ s β§tm w Ξ³β-Ξ³β)
      Ξ» w' Ο a b r-ab β
        let-bindR w' (ST.β¦ t β§tm Ξ³β) (N.β¦ t β§tm (N.rename-ctxt (Ο .ren) Ξ³β))
          (Ξ» b β a * b)
          _
          (β¦ t β§tm w' (ext-ctxt _ Ο Ξ³β-Ξ³β))
          Ξ» w'' Οβ aβ bβ r-aβbβ β
            trans (congβ _*_ r-ab r-aβbβ)
                  (eval-β b bβ (w'' .env))
  β¦ s `β€ t β§tm w {Ξ³β}{Ξ³β} Ξ³β-Ξ³β =
    let-bindR w (ST.β¦ s β§tm Ξ³β) (N.β¦ s β§tm Ξ³β)
      (Ξ» a β a β€α΅ ST.β¦ t β§tm Ξ³β)
      _
      (β¦ s β§tm w Ξ³β-Ξ³β)
      Ξ» w' Ο a b r-ab β
        let-bindR w' (ST.β¦ t β§tm Ξ³β) (N.β¦ t β§tm (N.rename-ctxt (Ο .ren) Ξ³β))
          (Ξ» b β a β€α΅ b)
          _
          (β¦ t β§tm w' (ext-ctxt _ Ο Ξ³β-Ξ³β))
          Ξ» w'' Οβ aβ bβ r-aβbβ β
            congβ _β€α΅_ (trans r-ab (ext-evalLinExp b Οβ)) r-aβbβ
  β¦ if s then t else u β§tm w {Ξ³β}{Ξ³β} Ξ³β-Ξ³β =
    let-bindR w (ST.β¦ s β§tm Ξ³β) (N.β¦ s β§tm Ξ³β)
      (Ξ» a β ifα΅ a then ST.β¦ t β§tm Ξ³β else ST.β¦ u β§tm Ξ³β)
      _
      (β¦ s β§tm w Ξ³β-Ξ³β)
      r
    where r : β w' (Ο : w' βw w) a b β
              β¦ Bool constraint β§ty w' a b β
              LetLiftR β¦ _ β§ty w'
                (ifα΅ a then ST.β¦ t β§tm Ξ³β else ST.β¦ u β§tm Ξ³β)
                (if b (N.β¦ t β§tm (N.rename-ctxt (Ο .ren) Ξ³β))
                      (Ξ» Ο' β N.β¦ u β§tm (N.rename-ctxt (Ο .ren β Ο') Ξ³β)))
          r w' Ο false b eq rewrite sym eq = β¦ u β§tm w' (ext-ctxt _ Ο Ξ³β-Ξ³β)
          r w' Ο true b eq rewrite sym eq = β¦ t β§tm w' (ext-ctxt _ Ο Ξ³β-Ξ³β)
  β¦ `Β¬ t β§tm w {Ξ³β}{Ξ³β} Ξ³β-Ξ³β =
    let-bindR w (ST.β¦ t β§tm Ξ³β) (N.β¦ t β§tm Ξ³β)
      not
      (Ξ» _ _ x β return (negate x))
      (β¦ t β§tm w Ξ³β-Ξ³β)
      Ξ» { w' Ο a b refl β eval-negate extFunc b (w' .env) }
  β¦ s `β§ t β§tm w {Ξ³β}{Ξ³β} Ξ³β-Ξ³β =
    let-bindR w (ST.β¦ s β§tm Ξ³β) (N.β¦ s β§tm Ξ³β)
      (Ξ» a β a β§ ST.β¦ t β§tm Ξ³β)
      _
      (β¦ s β§tm w Ξ³β-Ξ³β)
      Ξ» w' Ο a b r-ab β
        let-bindR w' (ST.β¦ t β§tm Ξ³β) (N.β¦ t β§tm (N.rename-ctxt (Ο .ren) Ξ³β))
          (Ξ» b β a β§ b)
          _
          (β¦ t β§tm w' (ext-ctxt _ Ο Ξ³β-Ξ³β))
          Ξ» w'' Οβ aβ bβ r-aβbβ β
          congβ _β§_ (trans r-ab (ext-evalConstraint b Οβ)) r-aβbβ
  β¦ s `β¨ t β§tm w {Ξ³β}{Ξ³β} Ξ³β-Ξ³β =
    let-bindR w (ST.β¦ s β§tm Ξ³β) (N.β¦ s β§tm Ξ³β)
      (Ξ» a β a β¨ ST.β¦ t β§tm Ξ³β)
      _
      (β¦ s β§tm w Ξ³β-Ξ³β)
      Ξ» w' Ο a b r-ab β
        let-bindR w' (ST.β¦ t β§tm Ξ³β) (N.β¦ t β§tm (N.rename-ctxt (Ο .ren) Ξ³β))
          (Ξ» b β a β¨ b)
          _
          (β¦ t β§tm w' (ext-ctxt _ Ο Ξ³β-Ξ³β))
          Ξ» w'' Οβ aβ bβ r-aβbβ β
          congβ _β¨_ (trans r-ab (ext-evalConstraint b Οβ)) r-aβbβ


    -- FIXME: lemmas for unary and binary operators?
    -- FIXME: would be easier to uncurry and have a lift2 operation:
    ---   lift2 : (A Γ B ββ C) β LetLift A β LetLift B β LetLift C
