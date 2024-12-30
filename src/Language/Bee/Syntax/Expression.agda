module Language.Bee.Syntax.Expression where

open import Prelude hiding (if_then_else_; _≡_; _≢_)

import Agda.Builtin.Bool as Agda
import Data.Int as Int

open import Language.Bee.Syntax.Common
open import Language.Bee.Syntax.Effect
open import Language.Bee.Syntax.Type


---- Expressions ---------------------------------------------------------------

infix  9 `_ _`:_  _!
infix  9 _u8 _u16 _u32 _u64
infix  9 _i8 _i16 _i32 _i64
-- infix  8 `¬_
infixl 8  _◂_
infix  7 reg⟨_⟩_
infixl 7 _`*_ -- _`/_ _`%_
-- infixr 7 _`∧_ _`∨_
infixl 6 _`+_ _`-_
infix  4 _`<_ _`≤_ _`≡_ _`≢_ _`≥_ _`>_
infix  1 `if_then_else_
infixr 0 val_`=_⨾_ var_`in_≔_⨾_ _≔_⨾_

record Module : Set
data Declaration : Set
data Parameter : Set
data Expression : Set
data Operation : Set
data Literal : Set
-- data Pattern : Set
Memory : Set
data IsValue : Expression → Set
data IsBasicValue : Expression → Set
Value BasicValue : Set

record Module where
  field
    declarations : List Declaration
    main : Expression

data Declaration where
  --TS Don't know why we need the `lvars` for, we can deduce them from the expression
  fun : Id → List Parameter → Effect → Type → Expression → Declaration
  val : Id → Expression → Declaration

data Parameter where
  _`:_ : Id → Type → Parameter

data Expression where
  `_ : Id → Expression
  _◂_ : Expression → List Expression → Expression
  lit : Literal → Expression
  opr : Operation → Expression
  val_`=_⨾_ : Id → Expression → Expression → Expression
  `if_then_else_ : Expression → Expression → Expression → Expression
  adr : Ix → Expression
  reg⟨_⟩_ : Memory → Expression → Expression

data Operation where
  alloc : Id → Expression → Operation
  load : Expression → Operation
  store : Expression → Expression → Operation
  run : Id → Expression → Operation
  panic : Operation
  calc : (Int → Int → Int) → Expression → Expression → Operation
  comp : (Int → Int → Agda.Bool) → Expression → Expression → Operation

data Literal where
  word : (s : Sign) → (w : Width) → Int → Literal
  True False ⟨⟩ : Literal

-- data Pattern where
--   `_ : Id → Pattern
--   lit : Literal → Pattern

Memory = List (Ix × BasicValue)


---- Values --------------------------------------------------------------------

data IsValue where
  v-lit : ∀ {l} → IsValue (lit l)
  -- v-opr : ∀ {o} → IsValue (opr o)
  v-adr : ∀ {a} → IsValue (adr a)

data IsBasicValue where
  b-lit : ∀ {l} → IsBasicValue (lit l)

Value = [ v ∈ Expression ∣ IsValue v ]
BasicValue = [ b ∈ Expression ∣ IsBasicValue b ]


---- Sugar ---------------------------------------------------------------------

pattern var_`in_≔_⨾_ x r e c = val x `= opr (alloc r e) ⨾ c
pattern _! e = opr (load e)
pattern _≔_⨾_ x e c = val "_" `= opr (store x e) ⨾ c
pattern _▶_◂_ x f xs = f ◂ (x ∷ xs)
-- pattern `with_←_◂_⨾_ xs f as e = f ◂ (as ∷ᴿ fn⟨xs⟩ e)

pattern _u8  n = lit (word unsigned  8bits n)
pattern _u16 n = lit (word unsigned 16bits n)
pattern _u32 n = lit (word unsigned 32bits n)
pattern _u64 n = lit (word unsigned 64bits n)

pattern _i8  n = lit (word signed  8bits n)
pattern _i16 n = lit (word signed 16bits n)
pattern _i32 n = lit (word signed 32bits n)
pattern _i64 n = lit (word signed 64bits n)

_`+_ _`-_ _`*_ : Expression → Expression → Expression
a `+ b = opr (calc Int._+_ a b)
a `- b = opr (calc Int._-_ a b)
a `* b = opr (calc Int._*_ a b)
-- a `/ b = opr (calc Int._/_ a b)
-- a `% b = opr (calc Int._%_ a b)

_`<_ _`≤_ _`≡_ _`≢_ _`≥_ _`>_ : Expression → Expression → Expression
a `< b = opr (comp Int._<ᵇ_ a b)
a `≤ b = opr (comp Int._≤ᵇ_ a b)
a `≡ b = opr (comp Int._≡ᵇ_ a b)
a `≢ b = opr (comp Int._≢ᵇ_ a b)
a `≥ b = opr (comp Int._≥ᵇ_ a b)
a `> b = opr (comp Int._>ᵇ_ a b)

-- infix 8 _[_] _[_,_] _[_,_,_] _[_,_,_,_] _[_,_,_,_,_]
-- pattern _[_] f a = f ◂ [ a ]
-- pattern _[_,_] f a b = f ◂ [ a , b ]
-- pattern _[_,_,_] f a b c = f ◂ [ a , b , c ]
-- pattern _[_,_,_,_] f a b c d = f ◂ [ a , b , c , d ]
-- pattern _[_,_,_,_,_] f a b c d e = f ◂ [ a , b , c , d , e ]


---- Examples ------------------------------------------------------------------

_ : Expression
_ = (+ 2) u8

_ : Declaration
_ =
  fun "min" [ "a" `: U8 , "b" `: U8 ] ∅ U8 (
    val "x" `= `"a" `* (+ 2) u8 ⨾
    `if `"a" `< `"b"
      then `"a"
      else `"b"
  )

{-
      val "c" `= `"a" `+ `"b" ⨾
      val "d" `= `"c" `* 2 u8 ⨾
      `"d"
      ‶2 u8
val eth-p-ipv4 = 0x0800

@section("xdp")
fun xdp-prog(ctx: xdp/md) -> i32
 match ctx.data       // Safe unpacking of data
 None -> xdp/Drop   // Implicit return
 Some(eth) ->       // Immutable variables by default
   val h-proto = eth.h-proto / Type inference
   h-proto.times { / Bounded loops only
     bpf/print(h_proto)
   }
   if h-proto == htons(eth-p-ipv4)
     then xdp/Pass
     else xdp/Drop
-}
