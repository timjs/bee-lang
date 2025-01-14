module Language.Bee.Syntax where


open import Language.Bee.Syntax.Common public
open import Language.Bee.Syntax.Effect public
open import Language.Bee.Syntax.Expression public

-- Here we import the module under the name `Type`,
-- so we can distinguish `Type.(Is)Basic` and `Type.(Is)Primitive` from the same names in `Expression`.
-- The price we have to pay is that we cannot use the identifier `Type` as well for (mono) types,
-- which we renamed to `Mono`.
import Language.Bee.Syntax.Type
module Type = Language.Bee.Syntax.Type
open Type hiding (IsBasic; Basic; IsPrimitive; Primitive; _≟_) public
