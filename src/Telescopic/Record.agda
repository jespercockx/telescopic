
module Telescopic.Record where

open import Builtin.Reflection

open import Prelude
  hiding   (_>>=_; _>>_; abs)
  renaming (_>>=′_ to _>>=_; _>>′_ to _>>_)

open import Tactic.Reflection.Substitute
open import Container.List using (forgetAny)

open import Telescopic.Base
open import Telescopic.Telescope

module _ (#pars : Nat) (fs : List Name) where

  abstractFields : Nat → Term → Term

  private
    abstractInArg : Nat → Arg Term → Arg Term
    abstractInArgs : Nat → List (Arg Term) → List (Arg Term)
    abstractInArgsDrop : Nat → Nat → List (Arg Term) → List (Arg Term)
    abstractInAbs : Nat → Abs Term → Abs Term
    abstractInSort : Nat → Sort → Sort

  abstractFields k (var x args)      =
    if x <? k
    then var x (abstractInArgs k args)
    else var (length fs + (x - 1)) (abstractInArgs k args)
  abstractFields k (con c args)      = con c (abstractInArgs k args)
  abstractFields k (def f args)      = case lookup∈ f fs of λ where
    (yes f∈fs) → var (k + forgetAny f∈fs) (abstractInArgsDrop (suc #pars) k args)
    (no x    ) → def f (abstractInArgs k args)
  abstractFields k (lam v t)         = lam v (abstractInAbs k t)
  abstractFields k (pat-lam cs args) = unknown -- TODO
  abstractFields k (pi a b)          = pi (abstractInArg k a) (abstractInAbs k b)
  abstractFields k (agda-sort s)     = agda-sort (abstractInSort k s)
  abstractFields k (lit l)           = lit l
  abstractFields k (meta x args)     = unknown -- TODO
  abstractFields k unknown           = unknown

  abstractInArg k (arg i x) = arg i (abstractFields k x)

  abstractInArgs k [] = []
  abstractInArgs k (x ∷ xs) = abstractInArg k x ∷ abstractInArgs k xs

  abstractInArgsDrop zero k xs = abstractInArgs k xs
  abstractInArgsDrop (suc toDrop) k [] = []
  abstractInArgsDrop (suc toDrop) k (x ∷ xs) = abstractInArgsDrop toDrop k xs

  abstractInAbs k (abs s x) = abs s (abstractFields (suc k) x)

  abstractInSort k (set t) = set (abstractFields k t)
  abstractInSort k (lit n) = lit n
  abstractInSort k unknown = unknown

{-# TERMINATING #-}
telView : Type → TC (List (String × Arg Type) × Type)
telView t = do
  pi a (abs x b) ← return t --TODO: reduce t (see #4585)
    where _ → return ([] , t)
  (tel , target) ← extendContext a (telView b)
  return (((x , a) ∷ tel) , target)

{-# TERMINATING #-}
dropPis : Nat → Type → TC Type
dropPis zero t = return t
dropPis (suc k) t = do
  pi a (abs _ b) ← return t --TODO: reduce t (see #4585)
    where _ → typeError (strErr "Should be a pi type: " ∷ termErr t ∷ [])
  extendContext a (dropPis k b)

unqualify : String → String
unqualify s =
  let xs = unpackString s
  in  packString (loop xs xs)
  where
    loop : List Char → List Char → List Char
    loop prev [] = prev
    loop prev (x ∷ xs) =
      if isYes (x == '.')
      then loop xs xs
      else loop prev xs

dropHidden : List (String × Arg Type) → List (String × Arg Type)
dropHidden [] = []
dropHidden xs@((x , a) ∷ xs') = case getVisibility a of λ where
  visible → xs
  _ → dropHidden xs'

addLams : List (String × Arg Type) → Term → Term
addLams [] t = t
addLams ((x , a) ∷ xs) t =
  (lam (getVisibility a) (abs x (addLams xs t)))

fieldsToTelescope : Nat → List (Arg Name) → List (Arg Name) → TC Term
fieldsToTelescope #pars []       prev-fs  =
  return (con (quote ∗) [])
fieldsToTelescope #pars (f ∷ fs) prev-fs = do
  f-type ← dropPis (suc #pars) =<< getType (unArg f)
  let f-abs-type = abstractFields #pars (map unArg prev-fs) 0 f-type
  fs-tel ← fieldsToTelescope #pars fs (f ∷ prev-fs)
  let lam-fs-tel = lam (getVisibility f) (abs (unqualify (show (unArg f))) fs-tel)
  return (con (quote _,_) (vArg f-abs-type ∷ vArg lam-fs-tel ∷ []))

macro
  recordToTelescope : Name → Term → TC ⊤
  recordToTelescope r goal = do
    record-type _ fs ← getDefinition r
      where
        _ → typeError (strErr "Not a definition: " ∷ nameErr r ∷ [])
    (pars , _) ← telView =<< getType r
    tel ← fieldsToTelescope (length pars) fs []
    let pars' = dropHidden pars
    let abs-tel = addLams pars' tel
    unify goal abs-tel

-- The telescope of the Σ-type
Σ-tel : ∀ {a b} (A : Set a) (B : A → Set b) → Tel _
Σ-tel = recordToTelescope Σ

test = ⟦ Σ-tel ℕ (Vec Bool) ⟧

_ : test ≡ Σ ℕ (λ x → Σ (Vec Bool x) (λ x₁ → ·))
_ = refl





-- -}
-- -}
-- -}
-- -}
