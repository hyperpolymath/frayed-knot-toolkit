module ChoreographicFrayedKnot where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)

data Strand : Set where
  S1 : Strand
  S2 : Strand
  S3 : Strand

data Orientation : Set where
  Over  : Orientation
  Under : Orientation

data Distinct : Strand → Strand → Set where
  S1S2 : Distinct S1 S2
  S1S3 : Distinct S1 S3
  S2S1 : Distinct S2 S1
  S2S3 : Distinct S2 S3
  S3S1 : Distinct S3 S1
  S3S2 : Distinct S3 S2

data Knot : Set where
  Unknot : Knot
  Cross  : (s-over s-under : Strand) →
           Distinct s-over s-under →
           Knot →
           Knot

data StrandPath : Set where
  Closed   : StrandPath
  Navigate : Orientation → Strand → StrandPath → StrandPath

data Maybe (A : Set) : Set where
  just    : A → Maybe A
  nothing : Maybe A

data _==_ : Strand → Strand → Set where
  same : ∀ {s} → s == s

==-sym : ∀ {x y : Strand} → x == y → y == x
==-sym same = same

strand-eq : (x y : Strand) → Maybe (x == y)
strand-eq S1 S1 = just same
strand-eq S1 S2 = nothing
strand-eq S1 S3 = nothing
strand-eq S2 S1 = nothing
strand-eq S2 S2 = just same
strand-eq S2 S3 = nothing
strand-eq S3 S1 = nothing
strand-eq S3 S2 = nothing
strand-eq S3 S3 = just same

strand-eq-refl : ∀ (s : Strand) → strand-eq s s ≡ just same
strand-eq-refl S1 = refl
strand-eq-refl S2 = refl
strand-eq-refl S3 = refl

distinct-not-equal : ∀ {x y : Strand} → Distinct x y → x == y → ⊥
distinct-not-equal S1S2 ()
distinct-not-equal S1S3 ()
distinct-not-equal S2S1 ()
distinct-not-equal S2S3 ()
distinct-not-equal S3S1 ()
distinct-not-equal S3S2 ()

project : Knot → Strand → StrandPath
project Unknot target = Closed
project (Cross s-over s-under d rest) target with strand-eq target s-over
... | just same = Navigate Over s-under (project rest target)
... | nothing with strand-eq target s-under
...   | just same = Navigate Under s-over (project rest target)
...   | nothing   = project rest target

project-over :
  ∀ {s-over s-under rest}
  (d : Distinct s-over s-under) →
  project (Cross s-over s-under d rest) s-over ≡
  Navigate Over s-under (project rest s-over)
project-over {s-over} {s-under} {rest} d
  rewrite strand-eq-refl s-over
  = refl

project-under :
  ∀ {s-over s-under rest}
  (d : Distinct s-over s-under) →
  project (Cross s-over s-under d rest) s-under ≡
  Navigate Under s-over (project rest s-under)
project-under {s-over} {s-under} {rest} d with strand-eq s-under s-over
... | just eq = ⊥-elim (distinct-not-equal d (==-sym eq))
... | nothing rewrite strand-eq-refl s-under = refl
