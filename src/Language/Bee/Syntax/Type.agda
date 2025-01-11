{-# OPTIONS --allow-unsolved-metas #-}
module Language.Bee.Syntax.Type where

import Data.String as String

open import Prelude
open import Language.Bee.Syntax.Common
open import Language.Bee.Syntax.Effect


---- Types ---------------------------------------------------------------------

infixl 8 _`?
infix  6 _⟨_⟩→_
infix  4 _≟_ --FIXME: move

data Sign : Set where
  signed : Sign
  unsigned : Sign

-- Nat∨Int : Sign → Set
-- Nat∨Int unsigned = Nat
-- Nat∨Int signed = Int

data Width : Set where
  8bits 16bits 32bits 64bits : Width

data Mono : Set
data IsPrimitive : Mono → Set
data IsBasic : Mono → Set
record Basic : Set
record Primitive : Set

data Mono where
  -- Arrows
  _⟨_⟩→_ : List Mono → Effect → Mono → Mono
  -- Options
  _`? : Mono → Mono
  -- References
  {-  #note[If we enforce a basic type here:
      - we need a translation from basic values to basic types,
        this is used to convert `Memory` to a `Context`;
      - our judgement for `new` needs a `IsBasic` predicate;
      - our judgments for `load`, `store`, and `adr` have a `β-ok`
        which can be reused.
      ]
  -}
  Ref : Id → (β : Mono) → {IsBasic β}  → Mono
  -- Primitives
  Unit Bool : Mono
  Word : Sign → Width → Mono

data IsPrimitive where
  π-Unit : IsPrimitive Unit
  π-Bool : IsPrimitive Bool
  π-Word : ∀ {s : Sign} {w : Width} → IsPrimitive (Word s w)

data IsBasic where
  β-Unit : IsBasic Unit
  β-Bool : IsBasic Bool
  β-Word : ∀ {s : Sign} {w : Width} → IsBasic (Word s w)
  β-Option : ∀ {β : Mono} → IsBasic β → IsBasic (β `?)

-- Basic = [ β ∈ Mono ∣ IsBasic β ]
record Basic where
  constructor _,_
  field
    type : Mono
    proof : IsBasic type

-- Primitive = [ π ∈ Mono ∣ IsPrimitive π ]
record Primitive where
  constructor _,_
  field
    type : Mono
    proof : IsPrimitive type

prim-is-basic : (τ : Mono) → (IsPrimitive τ) → IsBasic τ
prim-is-basic τ = {!   !}

β-Option-injective : ∀ {β} → IsBasic (β `?) → IsBasic β
β-Option-injective (β-Option ∃) = ∃

basic? : (β : Mono) → Dec (IsBasic β)
basic? (_ ⟨ _ ⟩→ _) = no (λ ())
basic? (Ref _ _) = no (λ ())
basic? (β `?) with basic? β
... | yes ∃ = yes (β-Option ∃)
... | no ¬∃ = no λ x → ¬∃ (β-Option-injective x)
basic? Unit = yes β-Unit
basic? Bool = yes β-Bool
basic? (Word _ _) = yes β-Word


---- Sugar ---------------------------------------------------------------------

pattern U8  = Word unsigned 8bits
pattern U16 = Word unsigned 16bits
pattern U32 = Word unsigned 32bits
pattern U64 = Word unsigned 64bits
pattern I8  = Word signed 8bits
pattern I16 = Word signed 16bits
pattern I32 = Word signed 32bits
pattern I64 = Word signed 64bits


---- Equality ------------------------------------------------------------------

_≟_ : (τ₁ : Mono) → (τ₂ : Mono) → Dec (τ₁ ≡ τ₂)
(τ⁺ ⟨ η ⟩→ τ₀) ≟ (τ′⁺ ⟨ η′ ⟩→ τ′₀) = yes {!   !}
(τ⁺ ⟨ η ⟩→ τ₀) ≟ τ₂ `? = no (λ ())
(τ⁺ ⟨ η ⟩→ τ₀) ≟ Ref h₂ τ₂ = no (λ ())
(τ⁺ ⟨ η ⟩→ τ₀) ≟ Unit = no (λ ())
(τ⁺ ⟨ η ⟩→ τ₀) ≟ Bool = no (λ ())
(τ⁺ ⟨ η ⟩→ τ₀) ≟ Word s₂ w₂ = no (λ ())

τ₁ `? ≟ (τ⁺ ⟨ η ⟩→ τ₀) = no (λ ())
τ₁ `? ≟ τ₂ `? = yes {!   !}
τ₁ `? ≟ Ref h₂ τ₂ = no (λ ())
τ₁ `? ≟ Unit = no (λ ())
τ₁ `? ≟ Bool = no (λ ())
τ₁ `? ≟ Word s₂ w₂ = no (λ ())

Ref h₁ τ₁ ≟ (τ⁺ ⟨ η ⟩→ τ₀) = no (λ ())
Ref h₁ τ₁ ≟ τ₂ `? = no (λ ())
Ref h₁ τ₁ ≟ Ref h₂ τ₂ = yes {!   !}
-- Ref h₁ τ₁ ≟ Ref h₂ τ₂ with h₁ String.≟ h₂ | τ₁ ≟ τ₂
-- ... | yes refl | yes refl = {!   !}
Ref h₁ τ₁ ≟ Unit = no (λ ())
Ref h₁ τ₁ ≟ Bool = no (λ ())
Ref h₁ τ₁ ≟ Word s₂ w₂ = no (λ ())

Unit ≟ (τ⁺ ⟨ η ⟩→ τ₀) = no (λ ())
Unit ≟ τ₂ `? = no (λ ())
Unit ≟ Ref h₂ τ₂ = no (λ ())
Unit ≟ Unit = yes refl
Unit ≟ Bool = no (λ ())
Unit ≟ Word s₂ w₂ = no (λ ())

Bool ≟ (τ⁺ ⟨ η ⟩→ τ₀) = no (λ ())
Bool ≟ τ₂ `? = no (λ ())
Bool ≟ Ref h₂ τ₂ = no (λ ())
Bool ≟ Unit = no (λ ())
Bool ≟ Bool = yes refl
Bool ≟ Word s₂ w₂ = no (λ ())

Word s₁ w₁ ≟ (τ⁺ ⟨ η ⟩→ τ₀) = no (λ ())
Word s₁ w₁ ≟ τ₂ `? = no (λ ())
Word s₁ w₁ ≟ Ref h₂ τ₂ = no (λ ())
Word s₁ w₁ ≟ Unit = no (λ ())
Word s₁ w₁ ≟ Bool = no (λ ())
Word s₁ w₁ ≟ Word s₂ w₂ = yes {!   !}
-- Word s₁ w₁ ≟ Word s₂ w₂ with s₁ Sign.≟ s₂ | w₁ Width.≟ w₂
-- ... | yes refl | yes refl = {!   !}


---- Primitives ----------------------------------------------------------------

-- ⌈_⌉ : ∀ {A B : Set} → (A → A → B) → Mono
-- ⌈ _+_ ⌉ = ∀ {s w} → [ Word s w , Word s w ] ⟨ ∅ ⟩→ Word s w


---- Examples ------------------------------------------------------------------

-- f→t : {A B C : Set} -> (A -> B -> C) -> Mono
-- f→t (_∧_) = [ Bool , Bool ] ⟨ [] ⟩→ Bool

-- ε₁ : Effect
-- ε₁ = Panic ∷ Diverge ∷ ∅ , {!   !}

-- ε₂ : Effect
-- ε₂ =  Diverge ∷ ∅ , {!   !}

-- ε∪ : Effect
-- ε∪ = ε₁ ++ ε₂
