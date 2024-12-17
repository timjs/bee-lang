module Language.Bee.Context where

import Data.String as String

open import Prelude
open import Language.Bee.Syntax hiding (∅)

infix  6 ⌈_⌉_ ⟦_⟧ᵀ
infixl 5 _,_⦂_ _++_
infix  4 _∋_⦂_


---- Contexts ------------------------------------------------------------------

data Context : Set where
  ∅ : Context
  _,_⦂_ : Context → Id → Type → Context

_++_ : Context → Context → Context
Γ ++ ∅ = Γ
Γ ++ (Γ′ , x ⦂ τ)  = (Γ , x ⦂ τ) ++ Γ′

data _∋_⦂_ : Context → Id → Type → Set where
  here : ∀ {Γ x τ} →
    ----------------
    Γ , x ⦂ τ ∋ x ⦂ τ
  there : ∀ {Γ x y τ σ} →
    x ≢ y →
    Γ ∋ x ⦂ τ →
    ----------------
    Γ , y ⦂ σ ∋ x ⦂ τ


---- Lookup --------------------------------------------------------------------

ext∋ : ∀ {Γ x x′ τ′} →
  x ≢ x′ →
  ¬ (∃[ τ ] Γ ∋ x ⦂ τ) →
  ----------------------------
  ¬ (∃[ τ ] Γ , x′ ⦂ τ′ ∋ x ⦂ τ)
ext∋ x≢x′ _ ⟨ τ , here ⟩ = x≢x′ refl
ext∋ _ ¬∃ ⟨ τ , there _ ∋x ⟩ = ¬∃ ⟨ τ , ∋x ⟩

lookup? :
  (Γ : Context) →
  (x : Id) →
  ------------------------
  Dec (∃[ τ ] Γ ∋ x ⦂ τ)
lookup? ∅ x = no (λ ())
lookup? (Γ , x′ ⦂ τ′) x with x String.≟ x′
... | yes refl = yes ⟨ τ′ , here ⟩
... | no x≢x′ with lookup? Γ x
...   | yes ⟨ τ , ∋x ⟩ = yes ⟨ τ , there x≢x′ ∋x ⟩
...   | no ¬∃ = no (ext∋ x≢x′ ¬∃)

---- Helpers -------------------------------------------------------------------

⟦_⟧ᵀ : BasicValue → Type
⟦ ⟨ lit (word s w _) ∣ _ ⟩ ⟧ᵀ = Word s w
⟦ ⟨ lit True ∣ _ ⟩ ⟧ᵀ = Bool
⟦ ⟨ lit False ∣ _ ⟩ ⟧ᵀ = Bool
⟦ ⟨ lit ⟨⟩ ∣ _ ⟩ ⟧ᵀ = Unit

-- This is the same operation as Leijen (2014) defines on heaps in Fig.5
⌈_⌉_ : Heap → Id → Context
⌈ [] ⌉ _ = ∅
⌈ ⟨ x , b ⟩ ∷ Θ ⌉ h = ⌈ Θ ⌉ h , x ⦂ ⟦ b ⟧ᵀ
