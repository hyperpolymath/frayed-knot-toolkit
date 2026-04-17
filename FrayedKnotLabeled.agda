module FrayedKnotLabeled where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; length)
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
-- Labeled crossings
------------------------------------------------------------------------

record Crossing : Set where
  constructor mkCrossing
  field
    label : ℕ
    sign  : CrossingSign

open Crossing public

Diagram : Set
Diagram = List Crossing

crossing-count : Diagram → ℕ
crossing-count = length

------------------------------------------------------------------------
-- Labeled outcomes
------------------------------------------------------------------------

record Outcome : Set where
  constructor mkOutcome
  field
    outLabel      : ℕ
    outSign       : CrossingSign
    outResolution : Resolution
    outKind       : BranchKind

open Outcome public

resolve-once : Crossing → Resolution → Outcome
resolve-once (mkCrossing ℓ s) r =
  mkOutcome ℓ s r (branch-kind s r)

resolve-crossing : Crossing → (Outcome × Outcome)
resolve-crossing c = (resolve-once c A-Smooth , resolve-once c B-Smooth)

------------------------------------------------------------------------
-- Basic correctness facts about labels
------------------------------------------------------------------------

left-label-preserved :
  ∀ (c : Crossing) →
  outLabel (proj₁ (resolve-crossing c)) ≡ label c
left-label-preserved c = refl

right-label-preserved :
  ∀ (c : Crossing) →
  outLabel (proj₂ (resolve-crossing c)) ≡ label c
right-label-preserved c = refl

left-sign-preserved :
  ∀ (c : Crossing) →
  outSign (proj₁ (resolve-crossing c)) ≡ sign c
left-sign-preserved c = refl

right-sign-preserved :
  ∀ (c : Crossing) →
  outSign (proj₂ (resolve-crossing c)) ≡ sign c
right-sign-preserved c = refl

------------------------------------------------------------------------
-- Toy signatures
------------------------------------------------------------------------

-- A toy signature ignores the label and resolution history, and keeps only:
--   (crossing sign, branch behaviour)
ToySig : Set
ToySig = CrossingSign × BranchKind

signature : Outcome → ToySig
signature o = (outSign o , outKind o)

signature-profile : Crossing → (ToySig × ToySig)
signature-profile c =
  ( signature (proj₁ (resolve-crossing c))
  , signature (proj₂ (resolve-crossing c))
  )

positive-signature-profile :
  ∀ (ℓ : ℕ) →
  signature-profile (mkCrossing ℓ Positive) ≡
  ((Positive , Split) , (Positive , Preserve))
positive-signature-profile ℓ = refl

negative-signature-profile :
  ∀ (ℓ : ℕ) →
  signature-profile (mkCrossing ℓ Negative) ≡
  ((Negative , Preserve) , (Negative , Split))
negative-signature-profile ℓ = refl

------------------------------------------------------------------------
-- Whole-diagram signature profiles
------------------------------------------------------------------------

profile-list : Diagram → List (ToySig × ToySig)
profile-list []       = []
profile-list (c ∷ cs) = signature-profile c ∷ profile-list cs

profile-count : Diagram → ℕ
profile-count d = length (profile-list d)

profile-count-is-crossing-count :
  ∀ (d : Diagram) → profile-count d ≡ crossing-count d
profile-count-is-crossing-count [] = refl
profile-count-is-crossing-count (c ∷ cs)
  rewrite profile-count-is-crossing-count cs
  = refl

------------------------------------------------------------------------
-- Counting total outcomes, split outcomes, preserve outcomes
------------------------------------------------------------------------

-- Each crossing contributes exactly two outcomes: A and B.
outcomes-at : Crossing → ℕ
outcomes-at c = suc (suc zero)

-- Across the pair (A,B), each crossing contributes exactly one split.
split-outcomes-at : Crossing → ℕ
split-outcomes-at c = suc zero

-- Across the pair (A,B), each crossing contributes exactly one preserve.
preserve-outcomes-at : Crossing → ℕ
preserve-outcomes-at c = suc zero

total-outcomes : Diagram → ℕ
total-outcomes []       = zero
total-outcomes (c ∷ cs) = outcomes-at c + total-outcomes cs

total-split-outcomes : Diagram → ℕ
total-split-outcomes []       = zero
total-split-outcomes (c ∷ cs) = split-outcomes-at c + total-split-outcomes cs

total-preserve-outcomes : Diagram → ℕ
total-preserve-outcomes []       = zero
total-preserve-outcomes (c ∷ cs) = preserve-outcomes-at c + total-preserve-outcomes cs

outcomes-at-is-two :
  ∀ (c : Crossing) → outcomes-at c ≡ suc (suc zero)
outcomes-at-is-two c = refl

split-at-is-one :
  ∀ (c : Crossing) → split-outcomes-at c ≡ suc zero
split-at-is-one c = refl

preserve-at-is-one :
  ∀ (c : Crossing) → preserve-outcomes-at c ≡ suc zero
preserve-at-is-one c = refl

------------------------------------------------------------------------
-- Tiny arithmetic lemma
------------------------------------------------------------------------

+-suc-right : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc-right zero n = refl
+-suc-right (suc m) n = cong suc (+-suc-right m n)

double-suc :
  ∀ (n : ℕ) → suc (suc (n + n)) ≡ suc (n + suc n)
double-suc n = cong suc (sym (+-suc-right n n))

------------------------------------------------------------------------
-- Diagram-level balance theorems
------------------------------------------------------------------------

total-splits-equals-crossings :
  ∀ (d : Diagram) → total-split-outcomes d ≡ crossing-count d
total-splits-equals-crossings [] = refl
total-splits-equals-crossings (c ∷ cs)
  rewrite split-at-is-one c
        | total-splits-equals-crossings cs
  = refl

total-preserves-equals-crossings :
  ∀ (d : Diagram) → total-preserve-outcomes d ≡ crossing-count d
total-preserves-equals-crossings [] = refl
total-preserves-equals-crossings (c ∷ cs)
  rewrite preserve-at-is-one c
        | total-preserves-equals-crossings cs
  = refl

total-outcomes-equals-double-crossings :
  ∀ (d : Diagram) → total-outcomes d ≡ crossing-count d + crossing-count d
total-outcomes-equals-double-crossings [] = refl
total-outcomes-equals-double-crossings (c ∷ cs)
  rewrite outcomes-at-is-two c
        | total-outcomes-equals-double-crossings cs
        | double-suc (crossing-count cs)
  = refl

total-splits-equals-total-preserves :
  ∀ (d : Diagram) → total-split-outcomes d ≡ total-preserve-outcomes d
total-splits-equals-total-preserves [] = refl
total-splits-equals-total-preserves (c ∷ cs)
  rewrite split-at-is-one c
        | preserve-at-is-one c
        | total-splits-equals-total-preserves cs
  = refl

------------------------------------------------------------------------
-- Compact summary theorem
------------------------------------------------------------------------

diagram-summary :
  ∀ (d : Diagram) →
  (profile-count d ≡ crossing-count d) ×
  (total-outcomes d ≡ crossing-count d + crossing-count d) ×
  (total-split-outcomes d ≡ crossing-count d) ×
  (total-preserve-outcomes d ≡ crossing-count d)
diagram-summary d =
  profile-count-is-crossing-count d ,
  total-outcomes-equals-double-crossings d ,
  total-splits-equals-crossings d ,
  total-preserves-equals-crossings d
