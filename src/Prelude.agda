module Prelude where


open import Data.Bool using (true; false; if_then_else_) public
open import Data.Empty using (⊥) public
open import Data.Int using (Int; +_) public
open import Data.List using (List; []; _∷_; zip) public
open import Data.List.Membership.Propositional using (_∈_; _∉_) public
open import Data.List.Relation.Unary.All using (All; all?) public
open import Data.Nat using () renaming (ℕ to Nat) public
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩) public
open import Data.Refinement using (Refinement-syntax) renaming (_,_ to ⟨_∣_⟩) public
open import Data.Sum using (_⊎_) renaming (inj₁ to wrong; inj₂ to right) public
open import Data.String using (String) public
open import Data.Vec using (Vec; []; _∷_) public
open import Data.Unit using (⊤) renaming (tt to ⟨⟩) public

open import Relation.Nullary using (Dec; yes; no; _because_) public
open import Relation.Nullary.Negation using (¬_) public
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong) public

open import Function using (_∘_; _|>_) public


infixr 8 _↦_

pattern _↦_ a b = ⟨ a , b ⟩
pattern ⟨_,_,_⟩ a b c = ⟨ a , ⟨ b , c ⟩ ⟩

-- This is defined in Data.List, but as a function, not as a pattern
-- and we want to use this notation in pattern synonyms
pattern [_] a = a ∷ []
pattern [_,_] a b = a ∷ b ∷ []
pattern [_,_,_] a b c = a ∷ b ∷ c ∷ []
pattern [_,_,_,_] a b c d = a ∷ b ∷ c ∷ d ∷ []
pattern [_,_,_,_,_] a b c d e = a ∷ b ∷ c ∷ d ∷ e ∷ []
