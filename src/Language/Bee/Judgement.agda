module Language.Bee.Judgement where

open import Prelude
open import Language.Bee.Context renaming (∅ to ∅ᶜ) public
open import Language.Bee.Syntax

infix  4 _⊢_⦂_∥_ _⊢ᴼ_⦂_∥_ _⊢ᴸ_⦂_


---- Typing judgements ---------------------------------------------------------

data _⊢ᴸ_⦂_ : Context → Literal → Type → Set where
  l-word : ∀ {Γ s w n} →
    -----------------------
    Γ ⊢ᴸ word s w n ⦂ Word s w
  l-true : ∀ {Γ} →
    ----------------
    Γ ⊢ᴸ True ⦂ Bool
  l-false : ∀ {Γ} →
    ----------------
    Γ ⊢ᴸ False ⦂ Bool
  l-unit : ∀ {Γ} →
    -------------
    Γ ⊢ᴸ ⟨⟩ ⦂ Unit

data _⊢ᴼ_⦂_∥_ : Context → Operation → Type → Effect → Set
data _⊢_⦂_∥_ : Context → Expression → Type → Effect → Set

-- Note: Only when making `IsBasic β` an instance argument of `Ref_`
-- *and* having an `IsBasic β` instance argument here
-- *and* giving it a name,
-- resolution will fill it in automatically in the `Ref_` constructor.
data _⊢ᴼ_⦂_∥_ where
  o-alloc : ∀ {Γ h e₁ β₁ η₁} →
    {β-ok : IsBasic β₁} →
    Γ ⊢ e₁ ⦂ β₁ ∥ η₁ →
    ---------------------------------------------------
    Γ ⊢ᴼ alloc h e₁ ⦂ Ref h β₁ {β-ok} ∥ Alloc h ∙ η₁
  o-load : ∀ {Γ h e₁ β₁ η₁} →
    {β-ok : IsBasic β₁} →
    Γ ⊢ e₁ ⦂ Ref h β₁ {β-ok} ∥ η₁ →
    --------------------------------------------------------
    Γ ⊢ᴼ load e₁ ⦂ β₁ ∥ Load h ∙ η₁
  o-store : ∀ {Γ h β₁₂ e₁ η₁ e₂ η₂} →
    {β-ok : IsBasic β₁₂} →
    Γ ⊢ e₁ ⦂ Ref h β₁₂ {β-ok} ∥ η₁ →
    Γ ⊢ e₁ ⦂ β₁₂ ∥ η₂ →
    -----------------------------------------------------------
    Γ ⊢ᴼ store e₁ e₂ ⦂ Unit ∥ Store h ∙ (η₁ ∪ η₂)
  o-panic : ∀ {Γ τ} →
    --------------------------------------
    Γ ⊢ᴼ panic ⦂ τ ∥ Panic ∙ ∅

data _⊢_⦂_∥_ where
  t-var : ∀ {Γ x τ} →
    Γ ∋ x ⦂ τ →
    --------------
    Γ ⊢ ` x ⦂ τ ∥ ∅
  t-app : ∀ {Γ e₀ e⁺ τ₀ τ⁺ η η₀ η⁺} →
    Γ ⊢ e₀ ⦂ τ⁺ ⟨ η₀ ⟩→ τ₀ ∥ η →
    All (λ {⟨ eᵢ , τᵢ ⟩ → ∀ {ηᵢ} → Γ ⊢ eᵢ ⦂ τᵢ ∥ ηᵢ × ηᵢ ⊆ η⁺}) (zip e⁺ τ⁺) →
    ------------------------------------------------------------------------
    Γ ⊢ e₀ ◂ e⁺ ⦂ τ₀ ∥ η ∪ η₀ ∪ η⁺
  -- t-app-1 : ∀ {Γ e₀ e⁺ τ₀ τ⁺ η η₀ η⁺} →
  --   Γ ⊢ e₀ ⦂ τ₁ ⟨ η ⟩→ τ₀ ∥ η₀ →
  --   Γ ⊢ e₁ ⦂ τ₁ ∥ η₁ →
  --   η₁ ⊆ η⁺}) (zip e⁺ τ⁺) →
  --   ------------------------------------------------------------------------
  --   Γ ⊢ e₀ ◂ e⁺ ⦂ τ₀ ∥ η ∪ η₀ ∪ η⁺
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
  t-adr : ∀ {Γ a h β} →
    {β-ok : IsBasic β} →
    ----------------------------------
    Γ ⊢ adr a ⦂ Ref h β {β-ok} ∥ ∅
  t-reg : ∀ {Γ Θ h e τ η} →
    Mutate h ⊆ η →
    Γ ++ ⌈ Θ ⌉ h ⊢ e ⦂ τ ∥ η →
    -------------------------
    Γ ⊢ reg⟨ Θ ⟩ e ⦂ τ ∥ η
  t-run : ∀ {Γ h e τ η} →
    Mutate h ⊆ η →
    Γ ⊢ e ⦂ τ ∥ η →
    ---------------------------------------------
    Γ ⊢ run e ⦂ τ ∥ (η ＼ Mutate h)
