module Language.Bee.Check where

open import Prelude
open import Language.Bee.Syntax.Common
open import Language.Bee.Syntax.Expression
open import Language.Bee.Syntax.Type
open import Data.Vec using (zip)
open import Data.Vec.Relation.Unary.All using (All)
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_)

infix  6 ⌈_⌉_ ⟦_⟧ᵀ
infixl 5 _++_
infixl 5 _,_⦂_
infix  4 _∋_⦂_ _⊢_⦂_∥_ _⊢ᴼ_⦂_∥_ _⊢ᴸ_⦂_


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


---- Helpers -------------------------------------------------------------------

⟦_⟧ᵀ : (e : Expression) → {BasicValue e} → Type
⟦ lit (word s w _) ⟧ᵀ = Word s w
⟦ lit `true ⟧ᵀ = Bool
⟦ lit `false ⟧ᵀ = Bool
⟦ lit ⟨⟩ ⟧ᵀ = Unit

⌈_⌉_ : Heap → Id → Context
⌈ ∅ ⌉ _ = ∅
⌈ ⟨ x , ⟨ v , p ⟩ ⟩ ∷ Θ ⌉ h = ⌈ Θ ⌉ h , x ⦂ ⟦ v ⟧ᵀ {p}


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
    --FIXME correct?
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
  t-ptr : ∀ {Γ a h β η} →
    (p : IsBasic β) →
    -------------------------------
    Γ ⊢ ptr a ⦂ Ref⟨ h , β ⟩ {p} ∥ η
  t-reg : ∀ {Γ Θ h e τ η} →
    Γ ++ ⌈ Θ ⌉ h ⊢ e ⦂ τ ∥ Modify⟨ h ⟩ ∷ η →
    ----------------------------------------
    Γ ⊢ reg⟨ Θ ⟩ e ⦂ τ ∥ Modify⟨ h ⟩ ∷ η
