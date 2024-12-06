module Language.Bee.Syntax.Type where

open import Prelude
open import Language.Bee.Syntax.Common

---- Types ---------------------------------------------------------------------

data Sign : Set where
  signed : Sign
  unsigned : Sign

data Size : Set where
  8bits 16bits 32bits 64bits : Size

data Effect : Set where
  panic, diverge : Effect
  alloc⟨_⟩, load⟨_⟩, store⟨_⟩ : Id → Effect

data Type : Set
data IsPrimitive : Type → Set
data IsBasic : Type → Set

data Type where
  -- Arrows
  _⟨_⟩→_ : ∀ {n : Nat} → Vec Type n → List Effect → Type
  -- References
  Ref⟨_⟩ : Id → (τ : Type) → {IsBasic τ} → Type
  -- Primitives
  Unit Bool : Type
  Word : Sign → Size → Type

data IsPrimitive where
  π-Unit : IsPrimitive Unit
  π-Bool : IsPrimitive Bool
  π-Word : ∀ {s : Sign} {b : Size} → IsPrimitive (Word s b)

data IsBasic where
  β-Unit : IsBasic Unit
  β-Bool : IsBasic Bool
  β-Word : ∀ {s : Sign} {b : Size} → IsBasic (Word s b)

pattern U8  = Word unsigned 8bits
pattern U16 = Word unsigned 16bits
pattern U32 = Word unsigned 32bits
pattern I8  = Word signed 8bits
pattern I16 = Word signed 16bits
pattern I32 = Word signed 32bits
