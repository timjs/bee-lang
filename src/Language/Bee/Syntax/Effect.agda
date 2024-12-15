module Language.Bee.Syntax.Effect where

open import Prelude
open import Language.Bee.Syntax.Common

import Data.String as String


---- Label ---------------------------------------------------------------------


data Label : Set where
  Panic Diverge : Label
  Alloc Load Store : Id → Label

alloc-injective : ∀{h₁ h₂} → Alloc h₁ ≡ Alloc h₂ → h₁ ≡ h₂
alloc-injective refl = refl

load-injective : ∀{h₁ h₂} → Load h₁ ≡ Load h₂ → h₁ ≡ h₂
load-injective refl = refl

store-injective : ∀{h₁ h₂} → Store h₁ ≡ Store h₂ → h₁ ≡ h₂
store-injective refl = refl

_≟_ : (l₁ : Label) → (l₂ : Label) → Dec (l₁ ≡ l₂)
Panic ≟ Panic = yes refl
Panic ≟ Diverge = no λ ()
Panic ≟ Alloc h = no λ ()
Panic ≟ Load h = no λ ()
Panic ≟ Store h = no λ ()

Diverge ≟ Panic = no λ ()
Diverge ≟ Diverge = yes refl
Diverge ≟ Alloc h = no λ ()
Diverge ≟ Load h = no λ ()
Diverge ≟ Store h = no λ ()

Alloc h ≟ Panic = no λ ()
Alloc h ≟ Diverge = no λ ()
Alloc h₁ ≟ Alloc h₂ with h₁ String.≟ h₂
... | yes refl = yes refl
... | no ¬h₁≡h₂ = no (¬h₁≡h₂ ∘ alloc-injective)
Alloc h₁ ≟ Load h₂ = no λ ()
Alloc h₁ ≟ Store h₂ = no λ ()

Load h ≟ Panic = no λ ()
Load h ≟ Diverge = no λ ()
Load h₁ ≟ Alloc h₂ = no λ ()
Load h₁ ≟ Load h₂ with h₁ String.≟ h₂
... | yes refl = yes refl
... | no ¬h₁≡h₂ = no (¬h₁≡h₂ ∘ load-injective)
Load h₁ ≟ Store h₂ = no λ ()

Store h ≟ Panic = no λ ()
Store h ≟ Diverge = no λ ()
Store h₁ ≟ Alloc h₂ = no λ ()
Store h₁ ≟ Load h₂ = no λ ()
Store h₁ ≟ Store h₂ with h₁ String.≟ h₂
... | yes refl = yes refl
... | no ¬h₁≡h₂ = no (¬h₁≡h₂ ∘ store-injective)


---- Effects -------------------------------------------------------------------

open import Data.Finset (_≟_) renaming (Finset to Effect) public

Mutate : Id → Effect
Mutate h = (Alloc h ∙ Load h ∙ Store h ∙ ∅)
