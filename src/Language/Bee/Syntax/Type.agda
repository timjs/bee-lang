module Language.Bee.Syntax.Type where

open import Prelude
open import Language.Bee.Syntax.Common
open import Language.Bee.Syntax.Effect

---- Types ---------------------------------------------------------------------

infix  7 Ref⟨_,_⟩
infix  6 _⟨_⟩→_

data Sign : Set where
  signed : Sign
  unsigned : Sign

Nat∨Int : Sign → Set
Nat∨Int unsigned = Nat
Nat∨Int signed = Int

data Width : Set where
  8bits 16bits 32bits 64bits : Width

data Type : Set
data IsPrimitive : Type → Set
data IsBasic : Type → Set
BasicType PrimitiveType : Set

data Type where
  -- Arrows
  _⟨_⟩→_ : ∀ {n : Nat} → Vec Type n → Effect → Type → Type
  -- References
  Ref⟨_,_⟩ : Id → BasicType → Type
  -- Primitives
  Unit Bool : Type
  Word : Sign → Width → Type

data IsPrimitive where
  π-Unit : IsPrimitive Unit
  π-Bool : IsPrimitive Bool
  π-Word : ∀ {s : Sign} {w : Width} → IsPrimitive (Word s w)

data IsBasic where
  β-Unit : IsBasic Unit
  β-Bool : IsBasic Bool
  β-Word : ∀ {s : Sign} {w : Width} → IsBasic (Word s w)

BasicType = [ β ∈ Type ∣ IsBasic β ]
PrimitiveType = [ π ∈ Type ∣ IsPrimitive π ]


---- Sugar ---------------------------------------------------------------------

pattern U8  = Word unsigned 8bits
pattern U16 = Word unsigned 16bits
pattern U32 = Word unsigned 32bits
pattern U64 = Word unsigned 64bits
pattern I8  = Word signed 8bits
pattern I16 = Word signed 16bits
pattern I32 = Word signed 32bits
pattern I64 = Word signed 64bits


---- Examples ------------------------------------------------------------------

-- f→t : {A B C : Set} -> (A -> B -> C) -> Type
-- f→t (_∧_) = [ Bool , Bool ] ⟨ [] ⟩→ Bool

-- ε₁ : Effect
-- ε₁ = Panic ∷ Diverge ∷ ∅ , {!   !}

-- ε₂ : Effect
-- ε₂ =  Diverge ∷ ∅ , {!   !}

-- ε∪ : Effect
-- ε∪ = ε₁ ++ ε₂
