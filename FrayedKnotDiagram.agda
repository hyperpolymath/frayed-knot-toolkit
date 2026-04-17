module FrayedKnotDiagram where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; length; foldr)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

------------------------------------------------------------------------
-- Basic local objects
------------------------------------------------------------------------

data Resolution : Set where
  A-Smooth : Resolution
  B-Smooth : Resolution

data CrossingSign : Set where
  Positive : CrossingSign
  Negative : CrossingSign

data BranchKind : Set where
  Split    : BranchKind
  Preserve : BranchKind

branch-kind : CrossingSign → Resolution → BranchKind
branch-kind Positive A-Smooth = Split
branch-kind Positive B-Smooth = Preserve
branch-kind Negative A-Smooth = Preserve
branch-kind Negative B-Smooth = Split

------------------------------------------------------------------------
-- Diagram model
------------------------------------------------------------------------

Diagram : Set
Diagram = List CrossingSign

crossing-count : Diagram → ℕ
crossing-count = length

------------------------------------------------------------------------
-- Counting outcomes per crossing
------------------------------------------------------------------------

outcomes-at : CrossingSign → ℕ
outcomes-at s = suc (suc zero)

split-outcomes-at : CrossingSign → ℕ
split-outcomes-at Positive = suc zero
split-outcomes-at Negative = suc zero

preserve-outcomes-at : CrossingSign → ℕ
preserve-outcomes-at Positive = suc zero
preserve-outcomes-at Negative = suc zero

total-outcomes : Diagram → ℕ
total-outcomes = foldr (λ s acc → outcomes-at s + acc) zero

total-split-outcomes : Diagram → ℕ
total-split-outcomes = foldr (λ s acc → split-outcomes-at s + acc) zero

total-preserve-outcomes : Diagram → ℕ
total-preserve-outcomes = foldr (λ s acc → preserve-outcomes-at s + acc) zero

------------------------------------------------------------------------
-- Local facts
------------------------------------------------------------------------

outcomes-at-is-two :
  ∀ (s : CrossingSign) → outcomes-at s ≡ suc (suc zero)
outcomes-at-is-two Positive = refl
outcomes-at-is-two Negative = refl

split-at-is-one :
  ∀ (s : CrossingSign) → split-outcomes-at s ≡ suc zero
split-at-is-one Positive = refl
split-at-is-one Negative = refl

preserve-at-is-one :
  ∀ (s : CrossingSign) → preserve-outcomes-at s ≡ suc zero
preserve-at-is-one Positive = refl
preserve-at-is-one Negative = refl

------------------------------------------------------------------------
-- Tiny arithmetic lemmas
------------------------------------------------------------------------

+-suc-right : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc-right zero n = refl
+-suc-right (suc m) n = cong suc (+-suc-right m n)

double-suc :
  ∀ (n : ℕ) → suc (suc (n + n)) ≡ suc (n + suc n)
double-suc n = cong suc (sym (+-suc-right n n))

------------------------------------------------------------------------
-- Diagram-level facts
------------------------------------------------------------------------

total-splits-equals-crossings :
  ∀ (d : Diagram) → total-split-outcomes d ≡ crossing-count d
total-splits-equals-crossings [] = refl
total-splits-equals-crossings (x ∷ xs)
  rewrite split-at-is-one x
        | total-splits-equals-crossings xs
  = refl

total-preserves-equals-crossings :
  ∀ (d : Diagram) → total-preserve-outcomes d ≡ crossing-count d
total-preserves-equals-crossings [] = refl
total-preserves-equals-crossings (x ∷ xs)
  rewrite preserve-at-is-one x
        | total-preserves-equals-crossings xs
  = refl

total-outcomes-equals-double-crossings :
  ∀ (d : Diagram) → total-outcomes d ≡ crossing-count d + crossing-count d
total-outcomes-equals-double-crossings [] = refl
total-outcomes-equals-double-crossings (x ∷ xs)
  rewrite outcomes-at-is-two x
        | total-outcomes-equals-double-crossings xs
        | double-suc (crossing-count xs)
  = refl

total-splits-equals-total-preserves :
  ∀ (d : Diagram) → total-split-outcomes d ≡ total-preserve-outcomes d
total-splits-equals-total-preserves [] = refl
total-splits-equals-total-preserves (x ∷ xs)
  rewrite split-at-is-one x
        | preserve-at-is-one x
        | total-splits-equals-total-preserves xs
  = refl

------------------------------------------------------------------------
-- Compact summary theorem
------------------------------------------------------------------------

diagram-resolution-balance :
  ∀ (d : Diagram) →
  ( total-outcomes d ≡ crossing-count d + crossing-count d ) ×
  ( total-split-outcomes d ≡ crossing-count d ) ×
  ( total-preserve-outcomes d ≡ crossing-count d )
diagram-resolution-balance d =
  total-outcomes-equals-double-crossings d ,
  total-splits-equals-crossings d ,
  total-preserves-equals-crossings d
