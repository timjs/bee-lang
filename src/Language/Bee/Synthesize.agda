module Language.Bee.Synthesize where

import Data.String as String
import Language.Bee.Syntax.Effect as Effect
import Language.Bee.Syntax.Type as Type

open import Prelude
open import Language.Bee.Syntax
open import Language.Bee.Judgement

check? : (Γ : Context) → (e : Expression) → (τ : Type) → (η : Effect) → Dec (Γ ⊢ e ⇐ τ ∥ η)
synthesizeᴾ : (Γ : Context) → (p : Primitive) → ∃[ τ ] Γ ⊢ᴾ p ⇒ τ
synthesize?ᴼ : (Γ : Context) → (o : Operation) → Dec (∃[ τ ] ∃[ η ] Γ ⊢ᴼ o ⇒ τ ∥ η)
synthesize? : (Γ : Context) → (e : Expression) → Dec (∃[ τ ] ∃[ η ] Γ ⊢ e ⇒ τ ∥ η)


check? Γ (run r e) τ η with check? Γ e τ (Mutate r ∪ η)
... | no ¬∃ = no {! no  !}
... | yes rule = yes (t-run rule {! free !})
check? Γ e τ η with synthesize? Γ e
... | no ¬∃ = {! no !}
... | yes (τ′ , η′ , rule) with τ′ Type.≟ τ | η′ ⊆? η
...   | no ¬∃₁ | no ¬∃₂ = no {! no !}
...   | yes ∃₁ | no ¬∃₂ = no {! no !}
...   | no ¬∃₁ | yes ∃₂ = no {! no !}
...   | yes τ′≡τ | yes η′⊆η = yes (t-sub rule τ′≡τ η′⊆η)


synthesizeᴾ Γ ⟨⟩ = (Unit , l-unit)
synthesizeᴾ Γ True = (Bool , l-true)
synthesizeᴾ Γ False = (Bool , l-false)
synthesizeᴾ Γ (word s w _) = (Word s w , l-word)


synthesize?ᴼ Γ (calc f e₁ e₂) with synthesize? Γ e₁ | synthesize? Γ e₂
... | no ¬∃₁ | no ¬∃₂ = no {! no !}
... | no ¬∃₁ | yes ∃₂ = no {! no !}
... | yes ∃₁ | no ¬∃₂ = no {! no !}
... | yes (τ₁ , η₁ , rule₁) | yes (τ₂ , η₂ , rule₂) with τ₁ Type.≟ τ₂
...   | no ¬∃ = {! no  !}
...   | yes refl = yes (τ₁ , η₁ ∪ η₂ , o-calc rule₁ rule₂)
-- FIXME: same proof => factor this out?
synthesize?ᴼ Γ (comp f e₁ e₂) with synthesize? Γ e₁ | synthesize? Γ e₂
... | no ¬∃₁ | no ¬∃₂ = no {! no  !}
... | no ¬∃₁ | yes ∃₂ = no {! no  !}
... | yes ∃₁ | no ¬∃₂ = no {! no  !}
... | yes (τ₁ , η₁ , rule₁) | yes (τ₂ , η₂ , rule₂) with τ₁ Type.≟ τ₂
...   | no ¬∃ = {! no  !}
...   | yes refl = yes (τ₁ , η₁ ∪ η₂ , o-comp rule₁ rule₂)


-- Note: all `yes` cases below prove soundness, all `no` cases completeness

-- Variables
synthesize? Γ (` x) with lookup? Γ x
... | no ¬∃ = no λ{ (τ , η , t-var ∋x) → ¬∃ (τ , ∋x) }
... | yes (τ , ∋x) = yes (τ , ∅ , t-var ∋x)

-- Functions and binding
synthesize? Γ (e ◂ e⁺) = {!   !}
-- synthesize? Γ (e ◂ e⁺) with synthesize? Γ e
-- ... | yes (τ⁺ ⟨ η₀ ⟩→ τ₀ , η , rule) with all? (λ {(eᵢ , τᵢ) → synthesize? Γ eᵢ}) (zip e⁺ τ⁺)
-- ...   | yes p = yes (τ₀ , η ∪ η₀ ∪ {!   !} , t-app rule {!   !})
-- ...   | no ¬p = no {! no  !}

synthesize? Γ (val x `= e ⨾ e₁) = {!   !}

-- Primitives
synthesize? Γ (prim p) with synthesizeᴾ Γ p
... | (τ , p-rule) = yes (τ , ∅ , t-prim p-rule)

synthesize? Γ (oper o) with synthesize?ᴼ Γ o
... | no ¬∃ = {! no  !}
... | yes (τ , η , o-rule) = yes (τ , η , t-oper o-rule)

synthesize? Γ (`if e₀ then e₁ else e₂) with synthesize? Γ e₀ | synthesize? Γ e₁ | synthesize? Γ e₂
... | no ¬∃₀ | no ¬∃₁ | no ¬∃₂ = no {! no  !}
... | yes ∃₀ | no ¬∃₁ | no ¬∃₂ = no {! no  !}
... | no ¬∃₀ | yes ∃₁ | no ¬∃₂ = no {! no  !}
... | no ¬∃₀ | no ¬∃₁ | yes ∃₂ = no {! no  !}
... | yes ∃₀ | yes ∃₁ | no ¬∃₂ = no {! no  !}
... | no ¬∃₀ | yes ∃₁ | yes ∃₂ = no {! no  !}
... | yes ∃₀ | no ¬∃₁ | yes ∃₂ = no {! no  !}
... | yes (Bool , η₀ , rule₀) | yes (τ₁ , η₁ , rule₁) | yes (τ₂ , η₂ , rule₂) with τ₁ Type.≟ τ₂
...   | no ¬τ₁≡τ₂ = no {! no  !}
...   | yes refl = yes (τ₁ , η₀ ∪ η₁ ∪ η₂ , t-if rule₀ rule₁ rule₂)

-- Optionals
synthesize? Γ (None τ) = yes (τ `? , ∅ , t-none)

synthesize? Γ (Some e) with synthesize? Γ e
... | no ¬∃ = no {! no  !}
... | yes (τ , η , rule) = yes (τ `? , η , t-some rule)

synthesize? Γ (`with x₀ ← e₀ else e₁ ⨾ e₂) with synthesize? Γ e₀
... | no ¬∃ = no {! no  !}
... | yes (τ₀ `? , η₀ , rule₀) with synthesize? Γ e₁ | synthesize? (Γ , x₀ ⦂ τ₀) e₂
...   | no ¬∃₁ | no ¬∃₂ = no {! no  !}
...   | yes ∃₁ | no ¬∃₂ = no {! no  !}
...   | no ¬∃₁ | yes ∃₂ = no {! no  !}
...   | yes (τ₁ , η₁ , rule₁) | yes (τ₂ , η₂ , rule₂) with τ₁ Type.≟ τ₂
...     | no ¬∃ = no {! no  !}
...     | yes refl = yes (τ₁ , η₀ ∪ η₁ ∪ η₂ , t-with rule₀ rule₁ rule₂)
synthesize? Γ (`with x₀ ← e₀ else e₁ ⨾ e₂) | yes (τ₀ , η₀ , rule₀) = no {! no  !}

-- References
synthesize? Γ (new r₁ e₁) with synthesize? Γ e₁
... | no ¬∃₁ = no {! no  !}
... | yes (β₁ , η₁ , rule₁) with basic? β₁
...   | no ¬β₁-ok = no {! no  !}
...   | yes β₁-ok = yes (Ref r₁ β₁ , Alloc r₁ ∙ η₁ , t-new rule₁ β₁-ok)

synthesize? Γ (e₁ !) with synthesize? Γ e₁
... | no ¬∃ = no {! no  !}
... | yes (Ref r₁ β₁ , η₁ , rule₁) with basic? β₁
...   | no ¬β₁-ok = no {! no  !}
...   | yes β₁-ok = yes (β₁ , Load r₁ ∙ η₁ , t-load rule₁ β₁-ok)
synthesize? Γ (e₁ !) | yes (τ₁ , η₁ , rule₁) = no {! no  !}

synthesize? Γ (e₁ ≔ e₂) with synthesize? Γ e₁ | synthesize? Γ e₂
... | no ¬∃₁ | no ¬∃₂ = no {! no  !}
... | no ¬∃₁ | yes ∃₂ = no {! no  !}
... | yes ∃₁ | no ¬∃₂ = no {! no  !}
... | yes (Ref r₁ β₁ , η₁ , rule₁) | yes (β₂ , η₂ , rule₂) with β₁ Type.≟ β₂
...   | no ¬∃β = {! no  !}
...   | yes refl with basic? β₁
...     | no ¬β-ok = no {! no  !}
...     | yes β-ok = yes (Unit , Store r₁ ∙ (η₁ ∪ η₂) , t-store rule₁ rule₂ β-ok)
synthesize? Γ (e₁ ≔ e₂) | yes (τ₁ , η₁ , rule₁) | yes (τ₂ , η₂ , rule₂) = no {! no  !}


synthesize? Γ (run r e) = {!   !}
synthesize? Γ (adr a) = yes ({! Ref h β  !} , ∅ , t-adr {!   !})
synthesize? Γ (reg⟨ Θ ⟩ e) with synthesize? (Γ ++ ⌈ Θ ⌉ {!   !}) e
... | no ¬∃ = no {! no  !}
... | yes (τ , η , rule) = yes (τ , η , t-reg {! Muth⊆η  !} rule)

{-
-- uninhabited-panic : ∀ {Γ τ η} → Γ ⊢ᴼ panic ⦂ τ ∥ η → ⊥
-- uninhabited-panic {Γ} {x ⟨ x₁ ⟩→ τ} {η} o-panic = {!   !}
-- uninhabited-panic {Γ} {Ref x τ} {η} o-panic = {!   !}
-- uninhabited-panic {Γ} {Unit} {η} o-panic = {!   !}
-- uninhabited-panic {Γ} {Bool} {η} o-panic = {! λ() !}
-- uninhabited-panic {Γ} {Word x x₁} {η} o-panic = {!   !}

-- unsynthesizable-panic : (Γ : Context) → (p : Dec (∃[ τ ] ∃[ η ] Γ ⊢ᴼ panic ⦂ τ ∥ η)) → ⊥
-- unsynthesizable-panic Γ p = {!   !}
-- -- unsynthesizable-panic Γ = λ
-- --   { (no ¬p) → {!   !}
-- --   ; (yes (τ , η , rule)) → {!   !}
-- --   }


check-τ? Γ e τ with synthesize? Γ e
... | no ¬p = {! no !}
... | yes (τ′ , η , rule) with τ′ Type.≟ τ
...   | no ¬p = {! no !}
...   | yes refl = yes (η , rule)

check-η? Γ e η with synthesize? Γ e
... | no ¬p = {! no !}
... | yes (τ , η′ , rule) with η′ Effect.⊆? η
...   | no ¬p = {! no !}
...   | yes p = yes (τ , {! goes wrong here, because η′ ⊆ η and not ≢ !})

-- inherit? Γ e τ η with synthesize? Γ e
-- ... | no ¬p = {!   !}
-- ... | yes (τ′ , η′ , rule) with τ′ Type.≟ τ | η′ Effect.≟ η
-- ...   | no ¬p | no ¬q = {! no !}
-- ...   | no ¬p | yes q = {! no !}
-- ...   | yes p | no ¬q = {! no !}
-- ...   | yes refl | yes refl = yes rule


-- synthesize?ᴼ Γ panic = yes ({! some-τ  !} , Panic ∙ ∅ , o-panic)
synthesize?ᴼ Γ panic = no λ x → {!   !}

synthesize?ᴼ Γ (calc f e₁ e₂) = {!   !}
synthesize?ᴼ Γ (comp f e₁ e₂) = {!   !}


-- apply?ᴼ :
--   (Γ : Context) →
--   (o : Operation) →
--   {e⁺ : List Expression} →
--   (τ⁺ : List Type) →
--   {all : All (λ { (eᵢ , τᵢ) → ∃[ ηᵢ ] Γ ⊢ eᵢ ⦂ τᵢ ∥ ηᵢ }) (zip e⁺ τ⁺)} →
--   -----------------------------------------------------------------
--   Dec (∃[ τ ] ∃[ η ] Γ ⊢ opr o ◂ e⁺ ⦂ τ ∥ η)
-- apply?ᴼ Γ alloc [ β ] with basic? β
-- ... | yes β-ok = yes (Ref {!   !} β {{β-ok}} , Alloc {!   !} ∙ ∅ , t-app (t-opr (o-alloc {{β-ok}})) {!   !})
-- ... | no ¬β-ok = no {!   !}
-- apply?ᴼ Γ load [ Ref h β ] with basic? β
-- ... | yes β-ok = yes {!   !}
-- ... | no ¬β-ok = no {!   !}
-- apply?ᴼ Γ store [ Ref h β₁ , β₂ ] with β₁ Type.≟ β₂
-- ... | yes β-ok = yes {!   !}
-- ... | no ¬β-ok = no {!   !}
-- apply?ᴼ Γ panic [] = {!   !}
-- -- apply?ᴼ Γ (calc _) = ({!   !} , {!   !})
-- -- apply?ᴼ Γ (comp _) = ({!   !} , {!   !})

-}

synthesize : (Γ : Context) → (e : Expression) → String ⊎ Type × Effect
synthesize Γ e with synthesize? Γ e
... | yes (τ , η , _) = right (τ , η)
... | no _ = wrong "Type error"

{-
yes (? , ? , ?)
-}
