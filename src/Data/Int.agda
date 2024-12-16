module Data.Int where

open import Data.Integer renaming (ℤ to Int) public

open import Data.Bool using (Bool; true; false; not; _∧_)
open import Relation.Nullary using (Dec; yes; no)
open import Function using (flip)


---- Boolean comparisons -------------------------------------------------------

infix  4 _≥ᵇ_ _<ᵇ_ _>ᵇ_ _≡ᵇ_ _≢ᵇ_

_≥ᵇ_ : Int → Int → Bool
_≥ᵇ_ = flip _≤ᵇ_

_≡ᵇ_ : Int → Int → Bool
x ≡ᵇ y with x ≟ y
... | yes _ = true
... | no  _ = false

_≢ᵇ_ : Int → Int → Bool
x ≢ᵇ y = not (x ≡ᵇ y)

_<ᵇ_ : Int → Int → Bool
x <ᵇ y = (x ≤ᵇ y) ∧ (x ≢ᵇ y)

_>ᵇ_ : Int → Int → Bool
x >ᵇ y = (x ≥ᵇ y) ∧ (x ≢ᵇ y)
