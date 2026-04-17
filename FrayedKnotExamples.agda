module FrayedKnotExamples where

open import Data.Nat using (zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import FrayedKnotLabeled

------------------------------------------------------------------------
-- Example diagrams
------------------------------------------------------------------------

allPositive₂ : Diagram
allPositive₂ =
  mkCrossing zero       Positive ∷
  mkCrossing (suc zero) Positive ∷
  []

mixed₂ : Diagram
mixed₂ =
  mkCrossing zero       Positive ∷
  mkCrossing (suc zero) Negative ∷
  []

------------------------------------------------------------------------
-- Explicit toy signatures and profiles
------------------------------------------------------------------------

posSplit : ToySig
posSplit = Positive , Split

posPreserve : ToySig
posPreserve = Positive , Preserve

negSplit : ToySig
negSplit = Negative , Split

negPreserve : ToySig
negPreserve = Negative , Preserve

posProfile : ToySig × ToySig
posProfile = posSplit , posPreserve

negProfile : ToySig × ToySig
negProfile = negPreserve , negSplit

------------------------------------------------------------------------
-- Computed profile lists
------------------------------------------------------------------------

allPositive₂-profiles :
  profile-list allPositive₂ ≡
  posProfile ∷
  posProfile ∷
  []
allPositive₂-profiles = refl

mixed₂-profiles :
  profile-list mixed₂ ≡
  posProfile ∷
  negProfile ∷
  []
mixed₂-profiles = refl

------------------------------------------------------------------------
-- Impossible equalities
------------------------------------------------------------------------

Positive≠Negative : Positive ≡ Negative → ⊥
Positive≠Negative ()

posProfile≠negProfile : posProfile ≡ negProfile → ⊥
posProfile≠negProfile ()

explicit-lists-different :
  posProfile ∷
  posProfile ∷
  []
  ≡
  posProfile ∷
  negProfile ∷
  []
  → ⊥
explicit-lists-different ()

------------------------------------------------------------------------
-- Main distinction theorem
------------------------------------------------------------------------

profiles-differ :
  profile-list allPositive₂ ≡ profile-list mixed₂ → ⊥
profiles-differ eq
  rewrite allPositive₂-profiles
        | mixed₂-profiles
  = explicit-lists-different eq
