```agda
module Language.Bee.Syntax.Common where

import Data.String as String

open import Prelude

Id : Set
Id = String

Ix : Set
Ix = String
-- Ix = Nat

open import Data.List.Membership.DecPropositional (String._≟_) using (_∈_; _∉_; _∈?_; _∉?_) public
```
