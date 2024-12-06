module Language.Bee.Syntax.Expression where

open import Prelude
open import Language.Bee.Syntax.Common
open import Language.Bee.Syntax.Type


---- Expressions ---------------------------------------------------------------

infix  9  `_ _`:_  _!
infix  9 _u8 _u16 _u32 _u64
infix  9 _i8 _i16 _i32 _i64
infix  8 `¬_
infixl 8  _∙_
infix  7 reg⟨_⟩_
infixl 7 _`*_ _`/_ _`%_
infixr 7 _`∧_ _`∨_
infixl 6 _`+_ _`-_
infix  4 _`<_ _`≤_ _`≡_ _`≢_ _`≥_ _`>_
infix  1 `if_then_else_
infixr 0 val_`=_⨾_ var_≔_⨾_ _≔_⨾_

module Operator where
  data Calculate : Set where
    add sub mul div mod : Calculate
  data Compare : Set where
    lt le eq ge gt nq : Compare

  data Reason : Set where
    and orr not : Reason
open Operator

record Module : Set
data Declaration : Set
data Parameter : Set
data Expression : Set
data Operation : Set
data Literal : Set
-- data Pattern : Set
Heap : Set
data Value : Expression → Set
data BasicValue : Expression → Set

record Module where
  field
    declarations : List Declaration
    main : Expression

data Declaration where
  --TS Don't know why you need the `lvars` for, you can deduce them from the expression
  fun : ∀ {n : Nat} → Id → Vec Parameter n → Expression → Declaration
  val : Id → Declaration

data Parameter where
  _`:_ : Id → Type → Parameter

data Expression where
  `_ : Id → Expression
  _∙_ : ∀ {n : Nat} → Expression → Vec Expression n → Expression
  lit : Literal → Expression
  opr : Operation → Expression
  val_`=_⨾_ : Id → Expression → Expression → Expression
  `if_then_else_ : Expression → Expression → Expression → Expression
  ptr : Ix → Expression
  reg⟨_⟩_ : Heap → Expression → Expression

data Operation where
  alloc load store run : Operation
  panic : Operation
  calc : Operator.Calculate → Operation
  comp : Operator.Compare → Operation
  resn : Operator.Reason → Operation

data Literal where
  word : (s : Sign) → (w : Width) → Nat∨Int s → Literal
  `true `false ⟨⟩ : Literal

-- data Pattern where
--   `_ : Id → Pattern
--   lit : Literal → Pattern

Heap = List (Id × Σ[ e ∈ Expression ] BasicValue e)


---- Values --------------------------------------------------------------------

data Value where
  v-lit : ∀ {l} → Value (lit l)
  v-opr : ∀ {o} → Value (opr o)
  v-ptr : ∀ {i} → Value (ptr i)

data BasicValue where
  b-lit : ∀ {l} → BasicValue (lit l)


---- Sugar ---------------------------------------------------------------------

pattern var_≔_⨾_ x e r = val x `= opr alloc ∙ [ e ] ⨾ r
pattern _! e = opr load ∙ [ e ]
pattern _≔_⨾_ x e r = val "_" `= opr store ∙ [ x , e ] ⨾ r
-- pattern `with_←_∙_⨾_ xs f as e = f ∙ (as ∷ fn⟨xs⟩ e)

pattern _u8  n = lit (word unsigned  8bits n)
pattern _u16 n = lit (word unsigned 16bits n)
pattern _u32 n = lit (word unsigned 32bits n)
pattern _u64 n = lit (word unsigned 64bits n)

pattern _i8  n = lit (word signed  8bits n)
pattern _i16 n = lit (word signed 16bits n)
pattern _i32 n = lit (word signed 32bits n)
pattern _i64 n = lit (word signed 64bits n)

pattern _`+_ a b = opr (calc add) ∙ [ a , b ]
pattern _`-_ a b = opr (calc sub) ∙ [ a , b ]
pattern _`*_ a b = opr (calc mul) ∙ [ a , b ]
pattern _`/_ a b = opr (calc div) ∙ [ a , b ]
pattern _`%_ a b = opr (calc mod) ∙ [ a , b ]

pattern _`<_ a b = opr (comp lt) ∙ [ a , b ]
pattern _`≤_ a b = opr (comp le) ∙ [ a , b ]
pattern _`≡_ a b = opr (comp eq) ∙ [ a , b ]
pattern _`≢_ a b = opr (comp nq) ∙ [ a , b ]
pattern _`≥_ a b = opr (comp ge) ∙ [ a , b ]
pattern _`>_ a b = opr (comp gt) ∙ [ a , b ]

pattern _`∧_ a b = opr (resn and) ∙ [ a , b ]
pattern _`∨_ a b = opr (resn orr) ∙ [ a , b ]
pattern  `¬_ a   = opr (resn not) ∙ [ a ]

-- infix 8 _[_] _[_,_] _[_,_,_] _[_,_,_,_] _[_,_,_,_,_]
-- pattern _[_] f a = f ∙ (a ∷ [])
-- pattern _[_,_] f a b = f ∙ (a ∷ b ∷ [])
-- pattern _[_,_,_] f a b c = f ∙ (a ∷ b ∷ c ∷ [])
-- pattern _[_,_,_,_] f a b c d = f ∙ (a ∷ b ∷ c ∷ d ∷ [])
-- pattern _[_,_,_,_,_] f a b c d e = f ∙ (a ∷ b ∷ c ∷ d ∷ e ∷ [])


---- Examples ------------------------------------------------------------------

_ : Expression
_ = 2 u8

_ : Declaration
_ =
  fun "min" [ "a" `: U8 , "b" `: U8 ] (
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
