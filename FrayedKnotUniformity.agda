module FrayedKnotUniformity where

open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import FrayedKnotLabeled
open import FrayedKnotExamples

------------------------------------------------------------------------
-- Uniformity of profile lists
------------------------------------------------------------------------

-- A list is uniform if all its entries are the same.
data Uniform {A : Set} : List A → Set where
  uniform[]  : Uniform []
  uniform[_] : ∀ {x} → Uniform (x ∷ [])
  uniform∷   : ∀ {x xs} → Uniform (x ∷ xs) → Uniform (x ∷ x ∷ xs)

-- A very small non-uniform witness for 2-element lists:
-- the first and second entries differ.
data NonUniform {A : Set} : List A → Set where
  nonuniform₂ : ∀ {x y} → (x ≡ y → ⊥) → NonUniform (x ∷ y ∷ [])

------------------------------------------------------------------------
-- allPositive₂ is uniform
------------------------------------------------------------------------

allPositive₂-uniform :
  Uniform (profile-list allPositive₂)
allPositive₂-uniform
  rewrite allPositive₂-profiles
  = uniform∷ uniform[_]

------------------------------------------------------------------------
-- mixed₂ is non-uniform
------------------------------------------------------------------------

mixed₂-nonuniform :
  NonUniform (profile-list mixed₂)
mixed₂-nonuniform
  rewrite mixed₂-profiles
  = nonuniform₂ posProfile≠negProfile
