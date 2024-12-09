module Data.List.NonDup where

open import Data.List using (List; _∷_; []; _++_)
import Data.List.Relation.Binary.Subset.Propositional as Subset

infixl 7 _∪_

-- Sets as lists of unique elements
-- opaque

List⁼ : (A : Set) → Set
List⁼ = List

∅ : ∀ {A} → List⁼ A
∅ = []

_,_ : ∀ {A} → (x : A) → (xs : List⁼ A) → List⁼ A
_,_ = _∷_

_∪_ : ∀ {A} → (xs : List⁼ A) → (ys : List⁼ A) → List⁼ A
_∪_ = _++_

_⊆_ : ∀ {A} → List⁼ A → List⁼ A → Set
_⊆_ = Subset._⊆_
