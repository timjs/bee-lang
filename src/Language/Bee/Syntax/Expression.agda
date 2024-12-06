module Language.Bee.Syntax.Expression where

open import Prelude
open import Language.Bee.Syntax.Common
open import Language.Bee.Syntax.Type


---- Expressions ---------------------------------------------------------------

infix  9  `_ _⦂_  _!
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
data Pattern : Set
data Operation : Set
data Literal : Set
data Heap : Set

record Module where
  field
    declarations : List Declaration
    main : Expression

data Declaration where
  --TS Don't know why you need the `lvars` for, you can deduce them from the expression
  fun : ∀ {n : Nat} → Id → Vec Parameter n → Expression → Declaration
  val : Id → Declaration

data Parameter where
  _⦂_ : Id → Type → Parameter

data Expression where
  `_ : Id → Expression
  _∙_ : ∀ {n : Nat} → Expression → Vec Expression n → Expression
  lit : Literal → Expression
  opr : Operation → Expression
  val_`=_⨾_ : Id → Pattern → Expression → Expression
  `if_then_else_ : Expression → Expression → Expression → Expression
  ptr : Ix → Expression
  reg⟨_⟩_ : Heap → Expression → Expression

data Operation where
  new get put run : Operation
  calc : Operator.Calculate → Operation
  comp : Operator.Compare → Operation
  reas : Operator.Reason -> Operation

data Literal where
  _u8 _u16 _u32 _u64 : Nat → Literal
  _i8 _i16 _i32 _i64 : Int → Literal
  true false ⟨⟩ : Literal

data Pattern where
  `_ : Id → Pattern
  lit : Literal → Pattern

data Heap where


---- Sugar ---------------------------------------------------------------------

pattern var_≔_⨾_ x e r = val x `= opr new ∙ [ e ] ⨾ r
pattern _! e = opr get ∙ [ e ]
pattern _≔_⨾_ x e r = val lit ⟨⟩ `= opr put ∙ [ x , e ] ⨾ r

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

pattern _`∧_ a b = opr (reas and) ∙ [ a , b ]
pattern _`∨_ a b = opr (reas orr) ∙ [ a , b ]
pattern  `¬_ a   = opr (reas not) ∙ [ a ]

-- infix 8 _[_] _[_,_] _[_,_,_] _[_,_,_,_] _[_,_,_,_,_]
-- pattern _[_] f a = f ∙ (a ∷ [])
-- pattern _[_,_] f a b = f ∙ (a ∷ b ∷ [])
-- pattern _[_,_,_] f a b c = f ∙ (a ∷ b ∷ c ∷ [])
-- pattern _[_,_,_,_] f a b c d = f ∙ (a ∷ b ∷ c ∷ d ∷ [])
-- pattern _[_,_,_,_,_] f a b c d e = f ∙ (a ∷ b ∷ c ∷ d ∷ e ∷ [])


---- Examples ------------------------------------------------------------------

_ : Expression
_ = lit (2 u8)

_ : Declaration
_ =
  fun "min" [ "a" ⦂ U8 , "b" ⦂ U8 ] (
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
