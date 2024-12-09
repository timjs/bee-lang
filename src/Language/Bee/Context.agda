module Language.Bee.Context where

open import Prelude
open import Language.Bee.Syntax

infix  6 ⌈_⌉_ ⟦_⟧ᵀ
infixl 5 _,_⦂_ _++_
infix  4 _∋_⦂_


---- Contexts ------------------------------------------------------------------

data Context : Set where
  ∅ᶜ : Context
  _,_⦂_ : Context → Id → Type → Context

_++_ : Context → Context → Context
Γ ++ ∅ᶜ = Γ
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


---- Helpers -------------------------------------------------------------------

⟦_⟧ᵀ : BasicValue → Type
⟦ ⟨ lit (word s w _) ∣ _ ⟩ ⟧ᵀ = Word s w
⟦ ⟨ lit `true ∣ _ ⟩ ⟧ᵀ = Bool
⟦ ⟨ lit `false ∣ _ ⟩ ⟧ᵀ = Bool
⟦ ⟨ lit ⟨⟩ ∣ _ ⟩ ⟧ᵀ = Unit

-- This is the same operation as Leijen (2014) defines on heaps in Fig.5
⌈_⌉_ : Heap → Id → Context
⌈ [] ⌉ _ = ∅ᶜ
⌈ ⟨ x , b ⟩ ∷ Θ ⌉ h = ⌈ Θ ⌉ h , x ⦂ ⟦ b ⟧ᵀ
