module Language.Bee.Syntax.Effect where

import Language.Bee.Syntax.Effect.Label as Label
open Label using (Alloc; Load; Store; Panic; Diverge) public

open import Prelude
open import Language.Bee.Syntax.Common

import Data.String as String


---- Effects -------------------------------------------------------------------

open import Data.Finset (Label._≟_) renaming (Finset to Effect) public

Mutate : Id → Effect
Mutate h = (Alloc h ∙ Load h ∙ Store h ∙ ∅)
