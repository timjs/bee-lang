module Language.Bee.Syntax where


open import Language.Bee.Syntax.Common public
open import Language.Bee.Syntax.Effect public
open import Language.Bee.Syntax.Expression public

import Language.Bee.Syntax.Type
module Type = Language.Bee.Syntax.Type
open Type hiding (IsBasic; Basic; IsPrimitive; Primitive; _≟_) public
