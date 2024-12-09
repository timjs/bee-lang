module Language.Bee.Check where

open import Prelude
open import Language.Bee.Context
open import Language.Bee.Syntax
open import Data.Vec using (zip)
open import Data.Vec.Relation.Unary.All using (All)

infix  4 _⊢_⦂_∥_ _⊢ᴼ_⦂_∥_ _⊢ᴸ_⦂_


---- Typing judgements ---------------------------------------------------------

data _⊢ᴸ_⦂_ : Context → Literal → Type → Set where
  l-word : ∀ {Γ s w n} →
    -----------------------
    Γ ⊢ᴸ word s w n ⦂ Word s w
  l-true : ∀ {Γ} →
    ---------------
    Γ ⊢ᴸ `true ⦂ Bool
  l-false : ∀ {Γ} →
    ---------------
    Γ ⊢ᴸ `false ⦂ Bool
  l-unit : ∀ {Γ} →
    -------------
    Γ ⊢ᴸ ⟨⟩ ⦂ Unit

data _⊢ᴼ_⦂_∥_ : Context → Operation → Type → Effect → Set where
  -- o-alloc : ∀ {Γ} →
  --   Γ ⊢ᴼ {!   !} ⦂ {!   !} ∥ {!   !}
  -- o-load : ∀ {Γ} →
  --   Γ ⊢ᴼ {!   !} ⦂ {!   !} ∥ {!   !}
  -- o-store : ∀ {Γ} →
  --   Γ ⊢ᴼ {!   !} ⦂ {!   !} ∥ {!   !}
  -- o-run : ∀ {Γ} →
  --   Γ ⊢ᴼ {!   !} ⦂ {!   !} ∥ {!   !}

data _⊢_⦂_∥_ : Context → Expression → Type → Effect → Set where
  t-var : ∀ {Γ x τ} →
    Γ ∋ x ⦂ τ →
    --------------
    Γ ⊢ ` x ⦂ τ ∥ ∅
  t-app : ∀ {Γ e₀ e⁺ τ₀ τ⁺ η η₀ η⁺} →
    Γ ⊢ e₀ ⦂ τ⁺ ⟨ η ⟩→ τ₀ ∥ η₀ →
    All (λ {⟨ eᵢ , τᵢ ⟩ → ∀ {ηᵢ} → Γ ⊢ eᵢ ⦂ τᵢ ∥ ηᵢ × ηᵢ ⊆ η⁺}) (zip e⁺ τ⁺) →
    ------------------------------------------------------------------------
    Γ ⊢ e₀ ∙ e⁺ ⦂ τ₀ ∥ η⁺ ∪ η ∪ η₀
  t-lit : ∀ {Γ l π} →
    Γ ⊢ᴸ l ⦂ π →
    ----------------
    Γ ⊢ lit l ⦂ π ∥ ∅
  t-opr : ∀ {Γ o τ η} →
    Γ ⊢ᴼ o ⦂ τ ∥ η →
    ----------------
    Γ ⊢ opr o ⦂ τ ∥ η
  t-let : ∀ {Γ x₁ e₁ e₀ τ₁ τ₀ η₁ η₀} →
    Γ ⊢ e₁ ⦂ τ₁ ∥ η₁ →
    Γ , x₁ ⦂ τ₁ ⊢ e₀ ⦂ τ₀ ∥ η₀ →
    -----------------------------------
    Γ ⊢ val x₁ `= e₁ ⨾ e₀ ⦂ τ₀ ∥ η₁ ∪ η₀
  t-cond : ∀ {Γ e₀ e₁ e₂ τ₁₂ η₀ η₁ η₂} →
    Γ ⊢ e₀ ⦂ Bool ∥ η₀ →
    Γ ⊢ e₁ ⦂ τ₁₂ ∥ η₁ →
    Γ ⊢ e₂ ⦂ τ₁₂ ∥ η₂ →
    ----------------------------------------------
    Γ ⊢ `if e₀ then e₁ else e₂ ⦂ τ₁₂ ∥ η₀ ∪ η₁ ∪ η₂
  t-adr : ∀ {Γ a h β η} →
    -- IsBasic β →
    -------------------------------
    Γ ⊢ adr a ⦂ Ref⟨ h , β ⟩ ∥ η
  t-reg : ∀ {Γ Θ h e τ η} →
    [ Alloc⟨ h ⟩ , Load⟨ h ⟩ , Store⟨ h ⟩ ] ⊆ η →
    Γ ++ ⌈ Θ ⌉ h ⊢ e ⦂ τ ∥ η →
    ----------------------------------------
    Γ ⊢ reg⟨ Θ ⟩ e ⦂ τ ∥ η
