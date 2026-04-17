module FrayedKnot where

open import Data.Nat using (ℕ; suc; _+_)
open import Data.List using (List; []; _∷_; length; foldr)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Basic objects
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

record TopologicalState : Set where
  constructor mkState
  field
    components : ℕ
    history    : List Resolution

open TopologicalState public

------------------------------------------------------------------------
-- Local crossing logic
------------------------------------------------------------------------

-- Positive crossing: A splits, B preserves
-- Negative crossing: A preserves, B splits
branch-kind : CrossingSign → Resolution → BranchKind
branch-kind Positive A-Smooth = Split
branch-kind Positive B-Smooth = Preserve
branch-kind Negative A-Smooth = Preserve
branch-kind Negative B-Smooth = Split

-- Change in component count caused by a local resolution
component-change : CrossingSign → Resolution → ℕ → ℕ
component-change s r c with branch-kind s r
... | Split    = suc c
... | Preserve = c

-- Apply one chosen resolution at one crossing
fray-once : CrossingSign → Resolution → TopologicalState → TopologicalState
fray-once s r (mkState c hist) =
  mkState (component-change s r c) (r ∷ hist)

-- Resolve a crossing both ways
fray-crossing : CrossingSign → TopologicalState → (TopologicalState × TopologicalState)
fray-crossing s st = (fray-once s A-Smooth st , fray-once s B-Smooth st)

------------------------------------------------------------------------
-- Structural facts
------------------------------------------------------------------------

fray-is-binary :
  ∀ (s : CrossingSign) (st : TopologicalState) →
  fray-crossing s st ≡ (proj₁ (fray-crossing s st) , proj₂ (fray-crossing s st))
fray-is-binary s st = refl

------------------------------------------------------------------------
-- Exact branch behaviour for positive crossings
------------------------------------------------------------------------

positive-A-is-split :
  branch-kind Positive A-Smooth ≡ Split
positive-A-is-split = refl

positive-B-is-preserve :
  branch-kind Positive B-Smooth ≡ Preserve
positive-B-is-preserve = refl

positive-A-increases :
  ∀ (c : ℕ) → component-change Positive A-Smooth c ≡ suc c
positive-A-increases c = refl

positive-B-preserves :
  ∀ (c : ℕ) → component-change Positive B-Smooth c ≡ c
positive-B-preserves c = refl

------------------------------------------------------------------------
-- Exact branch behaviour for negative crossings
------------------------------------------------------------------------

negative-A-is-preserve :
  branch-kind Negative A-Smooth ≡ Preserve
negative-A-is-preserve = refl

negative-B-is-split :
  branch-kind Negative B-Smooth ≡ Split
negative-B-is-split = refl

negative-A-preserves :
  ∀ (c : ℕ) → component-change Negative A-Smooth c ≡ c
negative-A-preserves c = refl

negative-B-increases :
  ∀ (c : ℕ) → component-change Negative B-Smooth c ≡ suc c
negative-B-increases c = refl

------------------------------------------------------------------------
-- Successor-state lemmas
------------------------------------------------------------------------

left-branch-positive :
  ∀ (c : ℕ) (hist : List Resolution) →
  proj₁ (fray-crossing Positive (mkState c hist)) ≡
  mkState (suc c) (A-Smooth ∷ hist)
left-branch-positive c hist = refl

right-branch-positive :
  ∀ (c : ℕ) (hist : List Resolution) →
  proj₂ (fray-crossing Positive (mkState c hist)) ≡
  mkState c (B-Smooth ∷ hist)
right-branch-positive c hist = refl

left-branch-negative :
  ∀ (c : ℕ) (hist : List Resolution) →
  proj₁ (fray-crossing Negative (mkState c hist)) ≡
  mkState c (A-Smooth ∷ hist)
left-branch-negative c hist = refl

right-branch-negative :
  ∀ (c : ℕ) (hist : List Resolution) →
  proj₂ (fray-crossing Negative (mkState c hist)) ≡
  mkState (suc c) (B-Smooth ∷ hist)
right-branch-negative c hist = refl

------------------------------------------------------------------------
-- Oppositeness of the two resolutions
------------------------------------------------------------------------

positive-resolutions-are-opposite :
  ∀ (c : ℕ) →
  (component-change Positive A-Smooth c ≡ suc c) ×
  (component-change Positive B-Smooth c ≡ c)
positive-resolutions-are-opposite c = refl , refl

negative-resolutions-are-opposite :
  ∀ (c : ℕ) →
  (component-change Negative A-Smooth c ≡ c) ×
  (component-change Negative B-Smooth c ≡ suc c)
negative-resolutions-are-opposite c = refl , refl

------------------------------------------------------------------------
-- Compact branch profile
------------------------------------------------------------------------

branch-profile : CrossingSign → (BranchKind × BranchKind)
branch-profile s = (branch-kind s A-Smooth , branch-kind s B-Smooth)

positive-profile :
  branch-profile Positive ≡ (Split , Preserve)
positive-profile = refl

negative-profile :
  branch-profile Negative ≡ (Preserve , Split)
negative-profile = refl

------------------------------------------------------------------------
-- Diagram-level counting
------------------------------------------------------------------------

-- Each crossing contributes exactly one split outcome across the pair (A,B).
count-split-at : CrossingSign → ℕ
count-split-at Positive = suc 0
count-split-at Negative = suc 0

-- Each crossing contributes exactly one preserve outcome across the pair (A,B).
count-preserve-at : CrossingSign → ℕ
count-preserve-at Positive = suc 0
count-preserve-at Negative = suc 0

count-splits : List CrossingSign → ℕ
count-splits = foldr (λ s acc → count-split-at s + acc) 0

count-preserves : List CrossingSign → ℕ
count-preserves = foldr (λ s acc → count-preserve-at s + acc) 0

split-per-crossing :
  ∀ (s : CrossingSign) → count-split-at s ≡ suc 0
split-per-crossing Positive = refl
split-per-crossing Negative = refl

preserve-per-crossing :
  ∀ (s : CrossingSign) → count-preserve-at s ≡ suc 0
preserve-per-crossing Positive = refl
preserve-per-crossing Negative = refl

split-count-equals-preserve-count :
  ∀ (xs : List CrossingSign) → count-splits xs ≡ count-preserves xs
split-count-equals-preserve-count [] = refl
split-count-equals-preserve-count (x ∷ xs)
  rewrite split-per-crossing x
        | preserve-per-crossing x
        | split-count-equals-preserve-count xs
  = refl

split-count-is-length :
  ∀ (xs : List CrossingSign) → count-splits xs ≡ length xs
split-count-is-length [] = refl
split-count-is-length (x ∷ xs)
  rewrite split-per-crossing x
        | split-count-is-length xs
  = refl

preserve-count-is-length :
  ∀ (xs : List CrossingSign) → count-preserves xs ≡ length xs
preserve-count-is-length [] = refl
preserve-count-is-length (x ∷ xs)
  rewrite preserve-per-crossing x
        | preserve-count-is-length xs
  = refl

diagram-balance :
  ∀ (xs : List CrossingSign) →
  (count-splits xs ≡ length xs) × (count-preserves xs ≡ length xs)
diagram-balance xs = split-count-is-length xs , preserve-count-is-length xs
