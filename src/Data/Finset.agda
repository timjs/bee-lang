open import Relation.Binary.Definitions using (DecidableEquality)

-- Finite sets as lists of unique elements parametrised by type A.
-- Needs DecidableEquality on this A.
module Data.Finset {A : Set} (_≟_ : DecidableEquality A) where

import Data.List.Relation.Binary.Subset.Propositional as Subset

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.DecPropositional (_≟_) using (_∈?_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (¬Any⇒All¬)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique; tail)
open import Data.List.Relation.Unary.AllPairs using (_∷_; [])
open import Data.Refinement using (Refinement-syntax)
open import Relation.Nullary.Decidable using (Dec; yes; no)


infixl 7 _∪_
infixr 6 _,_

record Finset : Set where
  constructor ⟨_∣_⟩
  field
    list : List A
    -- NOTE: cannot make this Irrelevant because of _∪_ below.
    unique-list : Unique list

∅ : Finset
∅ = ⟨ [] ∣ [] ⟩

_,_ : A → Finset → Finset
x , ⟨ xs ∣ unique-xs ⟩ with x ∈? xs
... | yes x∈xs = ⟨ xs ∣ unique-xs ⟩
... | no ¬x∈xs = ⟨ x ∷ xs ∣ ¬Any⇒All¬ xs ¬x∈xs ∷ unique-xs ⟩

_∪_ : Finset → Finset → Finset
⟨ [] ∣ _ ⟩ ∪ ys = ys
-- OK, but not with Irrelevant:
⟨ x ∷ xss ∣ _ ∷ unique-xss ⟩ ∪ ys = x , ⟨ xss ∣ unique-xss ⟩ ∪ ys
-- NOT OK, because of irrelevant pattern match:
-- ⟨ x ∷ xss ∣ .(_ ∷ unique-xss) ⟩ ∪ ys = x , ⟨ xss ∣ unique-xss ⟩ ∪ ys
-- NOT OK, because of lack of termination proof on `tail`:
-- ⟨ x ∷ xss ∣ unique-xs ⟩ ∪ ys = x , ⟨ xss ∣ tail unique-xs ⟩ ∪ ys
-- ⟨ x ∷ xss ∣ unique-xs@(_ ∷ _) ⟩ ∪ ys = x , ⟨ xss ∣ tail unique-xs ⟩ ∪ ys

_⊆_ : Finset → Finset → Set
⟨ xs ∣ _ ⟩ ⊆ ⟨ ys ∣ _ ⟩ = xs Subset.⊆ ys
