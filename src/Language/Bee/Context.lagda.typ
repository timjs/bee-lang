```agda
{-# OPTIONS --allow-unsolved-metas #-}
module Language.Bee.Context where

import Data.String as String

open import Prelude
open import Language.Bee.Syntax hiding (∅)

infix  6 ⌈_⌉∙_ ⌈_⌉ ⟦_⟧ᵀ
infixl 5 _,_⦂_ _++_
infix  4 _∋_⦂_


---- Contexts ------------------------------------------------------------------

data Context : Set where
  ∅ : Context
  _,_⦂_ : Context → Id → Mono → Context

_++_ : Context → Context → Context
Γ ++ ∅ = Γ
Γ ++ (Γ′ , x ⦂ τ)  = (Γ , x ⦂ τ) ++ Γ′

data _∋_⦂_ : Context → Id → Mono → Set where
  here : ∀ {Γ x τ} →
    ----------------
    Γ , x ⦂ τ ∋ x ⦂ τ
  there : ∀ {Γ x y τ σ} →
    x ≢ y →
    Γ ∋ x ⦂ τ →
    ----------------
    Γ , y ⦂ σ ∋ x ⦂ τ

-- _∌_⦂_ : Context → Id → Mono → Set
-- Γ ∌ x ⦂ τ = ¬ (Γ ∋ x ⦂ τ)
--
-- data _∋!_⦂_ : Context → Id → Mono → Set where
--   here : ∀ {Γ x τ} →
--     Γ ∌ x ⦂ τ →
--     ----------------
--     Γ , x ⦂ τ ∋! x ⦂ τ
--   there : ∀ {Γ x y τ σ} →
--     x ≢ y →
--     Γ ∋! x ⦂ τ →
--     ----------------
--     Γ , y ⦂ σ ∋! x ⦂ τ


---- Lookup --------------------------------------------------------------------

ext∋ : ∀ {Γ x x′ τ′} →
  x ≢ x′ →
  ¬ (∃[ τ ] Γ ∋ x ⦂ τ) →
  ----------------------------
  ¬ (∃[ τ ] Γ , x′ ⦂ τ′ ∋ x ⦂ τ)
ext∋ x≢x′ _ (τ , here) = x≢x′ refl
ext∋ _ ¬∃ (τ , there _ ∋x) = ¬∃ (τ , ∋x)

lookup? :
  (Γ : Context) →
  (x : Id) →
  ------------------------
  Dec (∃[ τ ] Γ ∋ x ⦂ τ)
lookup? ∅ x = no (λ ())
lookup? (Γ , x′ ⦂ τ′) x with x String.≟ x′
... | yes refl = yes (τ′ , here)
... | no x≢x′ with lookup? Γ x
...   | yes (τ , ∋x) = yes (τ , there x≢x′ ∋x)
...   | no ¬∃ = no (ext∋ x≢x′ ¬∃)

lookup-overloaded? :
  (Γ : Context) →
  (τ⁺ : List Mono) →
  ------------------------
  Dec (∃[ x₀ ] ∃[ τ₀ ] ∃[ η₀ ] Γ ∋ x₀ ⦂ τ⁺ ⟨ η₀ ⟩→ τ₀)
lookup-overloaded? ∅ τ⁺ = no λ ()
lookup-overloaded? (Γ , x₀ ⦂ τ⁺′ ⟨ η₀ ⟩→ τ₀) τ⁺ with τ⁺′ Type.≟⁺ τ⁺
... | yes refl = yes (x₀ , τ₀ , η₀ , here)
... | no _ with lookup-overloaded? Γ τ⁺
...   | yes (x₀ , τ₀ , η₀ , ∋τ⁺) = yes (x₀ , τ₀ , η₀ , there {!   !} {!   !})
...   | no _ = no {!   !}
lookup-overloaded? (Γ , x ⦂ τ) τ⁺ = no λ (x₀ , τ₀ , η₀ , i) → {! nop !}

-- lookup-overloaded? ∅ τ⁺ = no λ ()
-- lookup-overloaded? (Γ , x₀ ⦂ τ⁺′ ⟨ η₀ ⟩→ τ₀) τ⁺ with τ⁺′ Type.≟⁺ τ⁺
-- ... | yes refl with lookup-overloaded? Γ τ⁺
-- ...   | no ¬∃ = yes (x₀ , τ₀ , η₀ , here λ x → {! !})
-- ...   | yes (x₀′ , τ₀′ , η₀′ , rule₀) = no λ x → {!   !}
-- lookup-overloaded? (Γ , x₀ ⦂ τ⁺′ ⟨ η₀ ⟩→ τ₀) τ⁺ | no ¬∃ = no {!   !}
-- lookup-overloaded? (Γ , x ⦂ τ) τ⁺ = no {!   !}


---- Helpers -------------------------------------------------------------------

⟦_⟧ᵀ : Basic → Type.Basic
⟦ (prim (word s w _) , b-prim) ⟧ᵀ = (Word s w , β-Word)
⟦ (prim True , b-prim) ⟧ᵀ = (Bool , β-Bool)
⟦ (prim False , b-prim) ⟧ᵀ = (Bool , β-Bool)
⟦ (prim ⟨⟩ , b-prim) ⟧ᵀ = (Unit , β-Unit)
⟦ (None β , b-none b-other) ⟧ᵀ = (β `? , β-Option b-other)
⟦ (Some b , b-some b-other) ⟧ᵀ with ⟦ (b , b-other) ⟧ᵀ
... | (β , β-other) = (β `? , β-Option β-other)

-- This is the same as the bar-operation Leijen (2014) defines on heaps in Fig.5
-- However, because our references need to be of basic type,
-- we'd need a proof that every basic value is of a basic type.
-- This is provided by our translation function.
⌈_⌉∙_ : Memory → Id → Context
⌈ [] ⌉∙ _ = ∅
⌈ x ↦ b ∷ μ ⌉∙ r with ⟦ b ⟧ᵀ
... | (β , β-ok) = ⌈ μ ⌉∙ r , x ⦂ Ref r β {β-ok}

⌈_⌉ : List Parameter → Context
⌈ [] ⌉ = ∅
⌈ x `: τ ∷ ps ⌉ = ⌈ ps ⌉ , x ⦂ τ

-- Free memory variables in a context
free : Context → List Id
free ∅ = []
free (Γ , x ⦂ Ref m τ) = m ∷ free Γ
free (Γ , _ ⦂ _) = free Γ
```
