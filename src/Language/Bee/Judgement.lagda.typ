#import "/typ/commands.typ": *

= Typing judgements

This is the main module where we define our typing rules.
We use a bidirectional type system.
There are multiple relations we define,
which we'll describe below.

```agda
module Language.Bee.Judgement where

open import Prelude
open import Language.Bee.Context renaming (∅ to ∅ᶜ) public
open import Language.Bee.Syntax

infix  4 _⊢_⇐_∥_ _⊢_⇐_⇒_ _⊢_⇚_∥_
infix  4 _⊢_⇒_∥_ _⊢_⇒⁺_∥_
infix  4 _⊢ᴾ_⇒_ _⊢ᴼ_⇒_∥_
```

== Declarations

First, we have two checking relations.
// - `Γ ⊢ e ⇒ τ ∥ η` _checks_ expression `e` against type `τ` and effect set `η`.
- $Gamma infer e check tau with eta$ _checks_ expression $e$ against type $tau$ and effect set $eta$.
- $Gamma infer e check tau synth eta$ checks $e$ against type $tau$ and _synthesizes_ effect set $eta$.
```agda
data _⊢_⇐_∥_ : Context → Expression → Mono → Effect → Set
data _⊢_⇐_⇒_ : Context → Expression → Mono → Effect → Set
```

Next, we have multiple synthesize relations.
- $Gamma infer e synth tau with eta$ _synthesizes_ from expression $e$ type $tau$ and effect set $eta$.
- $Gamma infer e synths tau synths eta$ is similar, but for spines.
- $Gamma infer^O e synth tau with eta$ and $Gamma infer^P e synth tau$ synthesize for operations and primitives.
  As creating primitives have no effect, this relation leaves effect sets out.
```agda
data _⊢_⇒_∥_ : Context → Expression → Mono → Effect → Set
data _⊢_⇒⁺_∥_ : Context → List Expression → List Mono → Effect → Set
data _⊢ᴼ_⇒_∥_ : Context → Operation → Mono → Effect → Set
data _⊢ᴾ_⇒_ : Context → Primitive → Mono → Set
```

Synthesizing primitives is trivial.
```agda
data _⊢ᴾ_⇒_ where
  l-unit : ∀ {Γ} →
    --------------
    Γ ⊢ᴾ ⟨⟩ ⇒ Unit
  l-true : ∀ {Γ} →
    ---------------
    Γ ⊢ᴾ True ⇒ Bool
  l-false : ∀ {Γ} →
    ----------------
    Γ ⊢ᴾ False ⇒ Bool
  l-word : ∀ {Γ s w n} →
    -------------------------
    Γ ⊢ᴾ word s w n ⇒ Word s w
```

When synthesizing operations,
we synthesize the word sign and width of the first argument,
after which we check that the second argument has the same sign and width.
```agda
data _⊢ᴼ_⇒_∥_ where
  o-calc : ∀ {Γ e₁ η₁ e₂ η₂ s w f} →
    Γ ⊢ e₁ ⇒ Word s w ∥ η₁ →
    Γ ⊢ e₂ ⇐ Word s w ⇒ η₂ →
    -------------------------------
    Γ ⊢ᴼ calc f e₁ e₂ ⇒ Word s w ∥ η₁ ∪ η₂
  o-comp : ∀ {Γ e₁ η₁ e₂ η₂ s w f} →
    Γ ⊢ e₁ ⇒ Word s w ∥ η₁ →
    Γ ⊢ e₂ ⇐ Word s w ⇒ η₂ →
    -------------------------------
    Γ ⊢ᴼ comp f e₁ e₂ ⇒ Bool ∥ η₁ ∪ η₂
```

```agda
-- Note: Only when making `IsBasic β` an instance argument of `Ref_`
-- *and* having an `IsBasic β` instance argument here
-- *and* giving it a name,
-- resolution will fill it in automatically in the `Ref_` constructor;
-- we're making it a normal implicit here.
data _⊢_⇒_∥_ where
  -- Variables
  t-var : ∀ {Γ x τ} →
    Γ ∋ x ⦂ τ →
    --------------
    Γ ⊢ ` x ⇒ τ ∥ ∅
  -- Functions and binding
  t-app : ∀ {Γ e₀ e⁺ f τ₀ τ⁺ η η₀ η⁺} →
    Γ ⊢ e⁺ ⇒⁺ τ⁺ ∥ η⁺ →
    Γ ∋ f ⦂ τ⁺ ⟨ η₀ ⟩→ τ₀ →
    Γ ⊢ e₀ ⇐ τ⁺ ⟨ η₀ ⟩→ τ₀ ⇒ η →
    ------------------------------
    Γ ⊢ e₀ ◂ e⁺ ⇒ τ₀ ∥ η ∪ η⁺ ∪ η₀
  t-let : ∀ {Γ x₁ e₁ e₀ τ₁ τ₀ η₁ η₀} →
    Γ ⊢ e₁ ⇒ τ₁ ∥ η₁ →
    Γ , x₁ ⦂ τ₁ ⊢ e₀ ⇒ τ₀ ∥ η₀ →
    -----------------------------------
    Γ ⊢ val x₁ `= e₁ ⨾ e₀ ⇒ τ₀ ∥ η₁ ∪ η₀
  -- Primitives
  t-prim : ∀ {Γ p π} →
    Γ ⊢ᴾ p ⇒ π →
    ----------------
    Γ ⊢ prim p ⇒ π ∥ ∅
  t-oper : ∀ {Γ o τ η} →
    Γ ⊢ᴼ o ⇒ τ ∥ η →
    ----------------
    Γ ⊢ oper o ⇒ τ ∥ η
  t-if : ∀ {Γ e₀ e₁ e₂ τ₁₂ η₀ η₁ η₂} →
    Γ ⊢ e₀ ⇐ Bool ⇒ η₀ →
    Γ ⊢ e₁ ⇒ τ₁₂ ∥ η₁ →
    Γ ⊢ e₂ ⇒ τ₁₂ ∥ η₂ →
    ----------------------------------------------
    Γ ⊢ `if e₀ then e₁ else e₂ ⇒ τ₁₂ ∥ η₀ ∪ η₁ ∪ η₂
  -- Optionals
  t-none : ∀ {Γ τ} →
    ------------------
    Γ ⊢ None τ ⇒ τ `? ∥ ∅
  t-some : ∀ {Γ e₁ τ₁ η₁} →
    Γ ⊢ e₁ ⇒ τ₁ ∥ η₁ →
    ------------------------
    Γ ⊢ Some e₁ ⇒ τ₁ `? ∥ η₁
  t-with : ∀ {Γ x₀ e₀ e₁ e₂ τ₀ τ₁₂ η₀ η₁ η₂} →
    Γ ⊢ e₀ ⇒ τ₀ `? ∥ η₀ →
    Γ ⊢ e₁ ⇒ τ₁₂ ∥ η₁ →
    Γ , x₀ ⦂ τ₀ ⊢ e₂ ⇒ τ₁₂ ∥ η₂ →
    --------------------------------------------------
    Γ ⊢ `with x₀ ← e₀ else e₁ ⨾ e₂ ⇒ τ₁₂ ∥ η₀ ∪ η₁ ∪ η₂
  -- References
  t-new : ∀ {Γ r₁ e₁ β₁ η₁} →
    Γ ⊢ e₁ ⇒ β₁ ∥ η₁ →
    {β-ok : Type.IsBasic β₁} →
    ------------------------------------------------
    Γ ⊢ new r₁ e₁ ⇒ Ref r₁ β₁ {β-ok} ∥ Alloc r₁ ∙ η₁
  t-load : ∀ {Γ r e β β-ok η} →
    Γ ⊢ e ⇒ Ref r β {β-ok} ∥ η →
    ----------------------------
    Γ ⊢ e ! ⇒ β ∥ Load r ∙ η
  t-store : ∀ {Γ r₁ β₁₂ β₁₂-ok e₁ η₁ e₂ η₂} →
    Γ ⊢ e₁ ⇒ Ref r₁ β₁₂ {β₁₂-ok} ∥ η₁ →
    Γ ⊢ e₂ ⇒ β₁₂ ∥ η₂ →
    -----------------------------------------
    Γ ⊢ e₁ ≔ e₂ ⇒ Unit ∥ Store r₁ ∙ (η₁ ∪ η₂)
  t-adr : ∀ {Γ a r β β-ok} →
    Γ ∋ a ⦂ Ref r β {β-ok} →
    -----------------------
    Γ ⊢ adr a ⇒ Ref r β {β-ok} ∥ ∅
  -- Instead of making `Mutate r` _available_ as an effect
  -- (which needs a checking mode),
  -- we _synthesize_ τ and η and _remove_ the synthesized region effects from η
  -- `run` is is annotated with a region `r`,
  -- so we know which region to run and which `Mutate r` effect to remove.
  t-run : ∀ {Γ r e τ η} →
    Γ ⊢ e ⇒ τ ∥ η →
    r ∉ free Γ →
    ------------------------------
    Γ ⊢ run r e ⇒ τ ∥ η ＼ Mutate r
  t-mem : ∀ {Γ μ r e τ η} →
    Mutate r ⊆ η →
    Γ ++ ⌈ μ ⌉∙ r ⊢ e ⇒ τ ∥ η →
    --------------------------
    Γ ⊢ mem r μ e ⇒ τ ∥ η

data _⊢_⇒⁺_∥_ where
  s-nil : ∀ {Γ} →
    ---------------
    Γ ⊢ [] ⇒⁺ [] ∥ ∅
  s-cons : ∀ {Γ e₀ e⁺ τ₀ τ⁺ η₀ η⁺} →
    Γ ⊢ e₀ ⇒ τ₀ ∥ η₀ →
    Γ ⊢ e⁺ ⇒⁺ τ⁺ ∥ η⁺ →
    ------------------------------
    Γ ⊢ e₀ ∷ e⁺ ⇒⁺ τ₀ ∷ τ⁺ ∥ η₀ ∪ η⁺

data _⊢_⇐_⇒_ where
  t-chk : ∀ {Γ e τ τ′ η} →
    Γ ⊢ e ⇒ τ′ ∥ η →
    τ′ ≡ τ →
    ---------------
    Γ ⊢ e ⇐ τ ⇒ η

data _⊢_⇐_∥_ where
  t-sub : ∀ {Γ e τ τ′ η η′} →
    Γ ⊢ e ⇒ τ′ ∥ η′ →
    τ′ ≡ τ →
    η′ ⊆ η →
    -------------
    Γ ⊢ e ⇐ τ ∥ η


data _⊢_⇚_∥_ : Context → Declaration → Mono → Effect → Set where
  t-fun : ∀ {Γ x p⁺ e d τ τ⁺ τ₀ η η₀} →
    Γ ++ ⌈ p⁺ ⌉ ⊢ e ⇐ τ₀ ∥ η₀ →
    Γ , x ⦂ τ⁺ ⟨ η₀ ⟩→ τ₀ ⊢ d ⇚ τ ∥ η →
    -----------------------------------------
    Γ ⊢ fun x [ p⁺ ]⟨ η ⟩→ τ ＝ e ⨾ d ⇚ τ ∥ η
  t-val : ∀ {Γ x₀ e₀ τ₀ d τ η} →
    Γ ⊢ e₀ ⇒ τ₀ ∥ ∅ →
    Γ , x₀ ⦂ τ₀ ⊢ d ⇚ τ ∥ η →
    ----------------------------
    Γ ⊢ val x₀ ＝ e₀ ⨾ d ⇚ τ ∥ η
  t-main : ∀ {Γ e τ η} →
    Γ ⊢ e ⇐ τ ∥ η →
    -------------------------------
    Γ ⊢ main[]⟨ η ⟩→ τ ＝ e ⇚ τ ∥ η
```
