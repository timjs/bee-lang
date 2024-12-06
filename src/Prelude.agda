module Prelude where

open import Data.List using (List; _∷_; []) public
open import Data.Nat using () renaming (ℕ to Nat) public
open import Data.Integer using () renaming (ℤ to Int) public
open import Data.String using (String) public
open import Data.Vec using (Vec; _∷_; []) public
open import Function using (_∘_; _|>_) public

pattern [_] a = a ∷ []
pattern [_,_] a b = a ∷ b ∷ []
pattern [_,_,_] a b c = a ∷ b ∷ c ∷ []
pattern [_,_,_,_] a b c d = a ∷ b ∷ c ∷ d ∷ []
pattern [_,_,_,_,_] a b c d e = a ∷ b ∷ c ∷ d ∷ e ∷ []
