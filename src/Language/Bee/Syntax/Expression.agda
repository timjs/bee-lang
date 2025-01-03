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
infix  1 `if_then_else_ `with_←_else_⨾_
infixr 0 val_`=_⨾_ var_`in_≔_⨾_ _≔_⨾_

record Module : Set
data Declaration : Set
data Parameter : Set
data Expression : Set
data Operation : Set
data Primitive : Set
-- data Shape : Set
Memory : Set
data IsValue : Expression → Set
data IsBasicValue : Expression → Set
record Value : Set
record BasicValue : Set
-- Value : Set
-- BasicValue : Set

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
  -- Variables
  `_ : Id → Expression
  -- Functions and binding
  _◂_ : Expression → List Expression → Expression
  val_`=_⨾_ : Id → Expression → Expression → Expression
  -- Primitives
  prim : Primitive → Expression
  oper : Operation → Expression
  `if_then_else_ : Expression → Expression → Expression → Expression
  -- Optionals
  None : Type → Expression
  Some : Expression → Expression
  `with_←_else_⨾_ : Id → Expression → Expression → Expression → Expression
  -- References
  new : Id → Expression → Expression
  _! : Expression → Expression
  _≔_ : Expression → Expression → Expression
  run : Id → Expression → Expression
  -- Not intended to be used by the programmer
  adr : Ix → Expression
  reg⟨_⟩_ : Memory → Expression → Expression

data Operation where
  calc : (Int → Int → Int) → Expression → Expression → Operation
  comp : (Int → Int → Agda.Bool) → Expression → Expression → Operation

data Primitive where
  ⟨⟩ : Primitive
  True False : Primitive
  word : (s : Sign) → (w : Width) → Int → Primitive

-- data Shape where
--   `_ : Id → Shape
--   prim : Primitive → Shape

Memory = List (Ix × BasicValue)


---- Values --------------------------------------------------------------------

data IsValue where
  v-prim : ∀ {l} →
    --------------
    IsValue (prim l)
  v-adr : ∀ {a} →
    ---------------
    IsValue (adr a)
  v-none : ∀ {τ} →
    ----------------
    IsValue (None τ)
  v-some : ∀ {v} →
    IsValue v →
    ----------------
    IsValue (Some v)
  -- v-fun : ∀ {x τ⁺ τ₀ η} →
  --   Γ ⊢ x ⦂ τ⁺ ⟨ η ⟩→ τ₀ ∥ ∅
  --   ------------------------
  --   IsValue (` x)

data IsBasicValue where
  b-prim : ∀ {l} → IsBasicValue (prim l)
  b-none : ∀ {β} → IsBasic β → IsBasicValue (None β)
  b-some : ∀ {b} → IsBasicValue b → IsBasicValue (Some b)

b-some-injective : ∀ {b} → IsBasicValue (Some b) → IsBasicValue b
b-some-injective (b-some ∃) = ∃

-- Value = [ v ∈ Expression ∣ IsValue v ]
record Value where
  constructor ⟨_∣_⟩
  field
    expression : Expression
    proof : IsValue expression

-- BasicValue = [ b ∈ Expression ∣ IsBasicValue b ]
record BasicValue where
  -- Because `Memory` is part of `Expression`s,
  -- `BasicValue` is mutual recursive with it.
  inductive
  constructor ⟨_∣_⟩
  field
    expression : Expression
    proof : IsBasicValue expression


---- Sugar ---------------------------------------------------------------------

pattern var_`in_≔_⨾_ x r e c = val x `= new r e ⨾ c
-- pattern _! e = oper (load e)
pattern _≔_⨾_ x e c = val "_" `= (x ≔ e) ⨾ c
pattern _▶_◂_ x f xs = f ◂ (x ∷ xs)
-- pattern `with_←_◂_⨾_ xs f as c = f ◂ (as ∷ᴿ fn⟨ xs ⟩ c)

pattern _u8  n = prim (word unsigned  8bits n)
pattern _u16 n = prim (word unsigned 16bits n)
pattern _u32 n = prim (word unsigned 32bits n)
pattern _u64 n = prim (word unsigned 64bits n)

pattern _i8  n = prim (word signed  8bits n)
pattern _i16 n = prim (word signed 16bits n)
pattern _i32 n = prim (word signed 32bits n)
pattern _i64 n = prim (word signed 64bits n)

_`+_ _`-_ _`*_ : Expression → Expression → Expression
a `+ b = oper (calc Int._+_ a b)
a `- b = oper (calc Int._-_ a b)
a `* b = oper (calc Int._*_ a b)
-- a `/ b = oper (calc Int._/_ a b)
-- a `% b = oper (calc Int._%_ a b)

_`<_ _`≤_ _`≡_ _`≢_ _`≥_ _`>_ : Expression → Expression → Expression
a `< b = oper (comp Int._<ᵇ_ a b)
a `≤ b = oper (comp Int._≤ᵇ_ a b)
a `≡ b = oper (comp Int._≡ᵇ_ a b)
a `≢ b = oper (comp Int._≢ᵇ_ a b)
a `≥ b = oper (comp Int._≥ᵇ_ a b)
a `> b = oper (comp Int._>ᵇ_ a b)

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
