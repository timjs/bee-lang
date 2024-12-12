module Language.Bee.Syntax.Effect where

open import Prelude
open import Language.Bee.Syntax.Common

import Data.String as String


---- Label ---------------------------------------------------------------------

infix  7 Alloc⟨_⟩ Load⟨_⟩ Store⟨_⟩

data Label : Set where
  Panic Diverge : Label
  Alloc⟨_⟩ Load⟨_⟩ Store⟨_⟩ : Id → Label

alloc-injective : ∀{h₁ h₂} → Alloc⟨ h₁ ⟩ ≡ Alloc⟨ h₂ ⟩ → h₁ ≡ h₂
alloc-injective refl = refl

load-injective : ∀{h₁ h₂} → Load⟨ h₁ ⟩ ≡ Load⟨ h₂ ⟩ → h₁ ≡ h₂
load-injective refl = refl

store-injective : ∀{h₁ h₂} → Store⟨ h₁ ⟩ ≡ Store⟨ h₂ ⟩ → h₁ ≡ h₂
store-injective refl = refl

_≟_ : (l₁ : Label) → (l₂ : Label) → Dec (l₁ ≡ l₂)
Panic ≟ Panic = yes refl
Panic ≟ Diverge = no λ ()
Panic ≟ Alloc⟨ h ⟩ = no λ ()
Panic ≟ Load⟨ h ⟩ = no λ ()
Panic ≟ Store⟨ h ⟩ = no λ ()

Diverge ≟ Panic = no λ ()
Diverge ≟ Diverge = yes refl
Diverge ≟ Alloc⟨ h ⟩ = no λ ()
Diverge ≟ Load⟨ h ⟩ = no λ ()
Diverge ≟ Store⟨ h ⟩ = no λ ()

Alloc⟨ x ⟩ ≟ Panic = no λ ()
Alloc⟨ x ⟩ ≟ Diverge = no λ ()
Alloc⟨ h₁ ⟩ ≟ Alloc⟨ h₂ ⟩ with h₁ String.≟ h₂
... | yes refl = yes refl
... | no ¬h₁≡h₂ = no (¬h₁≡h₂ ∘ alloc-injective)
Alloc⟨ x ⟩ ≟ Load⟨ x₁ ⟩ = no λ ()
Alloc⟨ x ⟩ ≟ Store⟨ x₁ ⟩ = no λ ()

Load⟨ x ⟩ ≟ Panic = no λ ()
Load⟨ x ⟩ ≟ Diverge = no λ ()
Load⟨ x ⟩ ≟ Alloc⟨ x₁ ⟩ = no λ ()
Load⟨ h₁ ⟩ ≟ Load⟨ h₂ ⟩ with h₁ String.≟ h₂
... | yes refl = yes refl
... | no ¬h₁≡h₂ = no (¬h₁≡h₂ ∘ load-injective)
Load⟨ x ⟩ ≟ Store⟨ x₁ ⟩ = no λ ()

Store⟨ x ⟩ ≟ Panic = no λ ()
Store⟨ x ⟩ ≟ Diverge = no λ ()
Store⟨ x ⟩ ≟ Alloc⟨ x₁ ⟩ = no λ ()
Store⟨ x ⟩ ≟ Load⟨ x₁ ⟩ = no λ ()
Store⟨ h₁ ⟩ ≟ Store⟨ h₂ ⟩ with h₁ String.≟ h₂
... | yes refl = yes refl
... | no ¬h₁≡h₂ = no (¬h₁≡h₂ ∘ store-injective)


---- Effects -------------------------------------------------------------------

open import Data.Finset (_≟_) using (_∪_; ∅) renaming (Finset to Effect) public
