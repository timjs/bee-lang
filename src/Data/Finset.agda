{-# OPTIONS --allow-unsolved-metas #-}
open import Relation.Binary.Definitions using (DecidableEquality)

-- Finite sets as lists of unique elements parametrised by type A.
-- Needs DecidableEquality on this A.
module Data.Finset {A : Set} (_≟ᴬ_ : DecidableEquality A) where

import Data.List.Relation.Binary.Subset.Propositional as Subset

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Membership.DecPropositional (_≟ᴬ_) using (_∈_; _∈?_)
open import Data.List.Relation.Unary.Any using (Any; here; there; index)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (¬Any⇒All¬)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique; tail)
open import Data.List.Relation.Unary.AllPairs using (_∷_; [])
open import Data.Nat using () renaming (ℕ to Nat)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong)


---- Finsets -------------------------------------------------------------------

infix  8 _∙⟨_∣_⟩
infixl 7 _∪_
infixr 6 _∙_
infix  4 _⊆_ _⊇_ _⊈_ _⊉_

record Finset : Set where
  constructor ⟨_∣_⟩
  field
    list : List A
    -- NOTE: cannot make this Irrelevant because of _∪_ below.
    unique-list : Unique list
open Finset


---- Construction --------------------------------------------------------------

pattern ∅ = ⟨ [] ∣ [] ⟩

pattern _∙⟨_∣_⟩ x xs unique-xs = ⟨ x ∷ xs ∣ _ ∷ unique-xs ⟩

_∙_ : A → Finset → Finset
x ∙ ⟨ xs ∣ unique-xs ⟩ with x ∈? xs
... | yes x∈xs = ⟨ xs ∣ unique-xs ⟩
... | no ¬x∈xs = ⟨ x ∷ xs ∣ ¬Any⇒All¬ xs ¬x∈xs ∷ unique-xs ⟩

_∪_ : Finset → Finset → Finset
∅ ∪ ys = ys
-- OK, but not with Irrelevant:
x ∙⟨ xs ∣ unique-xs ⟩ ∪ ys = x ∙ ⟨ xs ∣ unique-xs ⟩ ∪ ys
-- NOT OK, because of irrelevant pattern match:
-- ⟨ x ∷ xss ∣ .(_ ∷ unique-xss) ⟩ ∪ ys = x ∙ ⟨ xss ∣ unique-xss ⟩ ∪ ys
-- NOT OK, because of lack of termination proof on `tail`:
-- ⟨ x ∷ xss ∣ unique-xs ⟩ ∪ ys = x ∙ ⟨ xss ∣ tail unique-xs ⟩ ∪ ys
-- ⟨ x ∷ xss ∣ unique-xs@(_ ∷ _) ⟩ ∪ ys = x ∙ ⟨ xss ∣ tail unique-xs ⟩ ∪ ys

size : Finset → Nat
size ⟨ xs ∣ _ ⟩ = length xs

remove : A → Finset → Finset
remove x ⟨ xs ∣ unique-xs ⟩ = remove' x xs unique-xs where
-- remove x ∅ = ∅
-- remove x (y ∙⟨ ys ∣ unique-ys ⟩) with x ≟ᴬ y
-- ... | yes x≡y = ⟨ ys ∣ unique-ys ⟩
-- Note: Not very efficient! Checks if `y ∈ rec` again!
-- ... | no ¬x≡y = y ∙ remove x ⟨ ys ∣ unique-ys ⟩

  -- Trick to make `remove` terminate
  remove' : A → (xs : List A) → Unique xs → Finset
  remove' x [] [] = ∅
  remove' x (y ∷ ys) (_ ∷ unique-ys) with x ≟ᴬ y
  ... | yes x≡y = ⟨ ys ∣ unique-ys ⟩
  -- Note: Not very efficient! Checks if `y ∈ rec` again!
  ... | no ¬x≡y = y ∙ remove' x ys unique-ys

_＼_ : Finset → Finset → Finset
xs ＼ ∅ = xs
xs ＼ ⟨ y ∷ ys ∣ _ ∷ unique-ys ⟩ = remove y xs ＼ ⟨ ys ∣ unique-ys ⟩


---- Predicates ----------------------------------------------------------------

_⊆_ : Finset → Finset → Set
⟨ xs ∣ _ ⟩ ⊆ ⟨ ys ∣ _ ⟩ = xs Subset.⊆ ys

_⊇_ : Finset → Finset → Set
⟨ xs ∣ _ ⟩ ⊇ ⟨ ys ∣ _ ⟩ = xs Subset.⊇ ys

_⊈_ : Finset → Finset → Set
⟨ xs ∣ _ ⟩ ⊈ ⟨ ys ∣ _ ⟩ = xs Subset.⊈ ys

_⊉_ : Finset → Finset → Set
⟨ xs ∣ _ ⟩ ⊉ ⟨ ys ∣ _ ⟩ = xs Subset.⊉ ys

_⊆?_ : (xs : Finset) → (ys : Finset) → Dec (xs ⊆ ys)
_⊆?_ xs ys = {!   !}
