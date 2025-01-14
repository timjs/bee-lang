module Language.Bee.Synthesize where

import Data.String as String

open import Prelude
open import Language.Bee.Syntax
open import Language.Bee.Judgement

run-synthesize-uninhabited : ∀ {Γ r e τ η} → ¬ (Γ ⊢ run r e ⇒ τ ∥ η)
run-synthesize-uninhabited = λ ()

check? : (Γ : Context) → (e : Expression) → (τ : Mono) → (η : Effect) → Dec (Γ ⊢ e ⇐ τ ∥ η)
synthesizeᴾ : (Γ : Context) → (p : Primitive) → ∃[ τ ] Γ ⊢ᴾ p ⇒ τ
synthesize?ᴼ : (Γ : Context) → (o : Operation) → Dec (∃[ τ ] ∃[ η ] Γ ⊢ᴼ o ⇒ τ ∥ η)
synthesize? : (Γ : Context) → (e : Expression) → Dec (∃[ τ ] ∃[ η ] Γ ⊢ e ⇒ τ ∥ η)


check? Γ (run r e) τ η with check? Γ e τ (Mutate r ∪ η)
... | no ¬∃ = no {! no  !}
... | yes rule with r ∉? free Γ
...   | no ¬r∉Γ = no {! no !}
...   | yes r∉Γ = yes (t-run rule r∉Γ)
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
synthesize? Γ (e ◂ e⁺) = {! TODO: app  !}
-- synthesize? Γ (e ◂ e⁺) with synthesize? Γ e
-- ... | yes (τ⁺ ⟨ η₀ ⟩→ τ₀ , η , rule) with all? (λ {(eᵢ , τᵢ) → synthesize? Γ eᵢ}) (zip e⁺ τ⁺)
-- ...   | yes p = yes (τ₀ , η ∪ η₀ ∪ {!   !} , t-app rule {!   !})
-- ...   | no ¬p = no {! no  !}

synthesize? Γ (val x `= e ⨾ e₁) = {! TODO: let  !}

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
synthesize? Γ (`if e₀ then e₁ else e₂) | yes (τ₀ , η₀ , rule₀) | yes (τ₁ , η₁ , rule₁) | yes (τ₂ , η₂ , rule₂) = no {! no  !}

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
...   | yes β₁-ok = yes (Ref r₁ β₁ {β₁-ok}, Alloc r₁ ∙ η₁ , t-new rule₁ {β₁-ok})

synthesize? Γ (e₁ !) with synthesize? Γ e₁
... | no ¬∃ = no {! no  !}
... | yes (Ref r₁ β₁ , η₁ , rule₁) with basic? β₁
...   | no ¬β₁-ok = no {! no  !}
...   | yes β₁-ok = yes (β₁ , Load r₁ ∙ η₁ , t-load rule₁)
synthesize? Γ (e₁ !) | yes (τ₁ , η₁ , rule₁) = no {! no  !}

synthesize? Γ (e₁ ≔ e₂) with synthesize? Γ e₁ | synthesize? Γ e₂
... | no ¬∃₁ | no ¬∃₂ = no {! no  !}
... | no ¬∃₁ | yes ∃₂ = no {! no  !}
... | yes ∃₁ | no ¬∃₂ = no {! no  !}
... | yes (Ref r₁ β₁ , η₁ , rule₁) | yes (β₂ , η₂ , rule₂) with β₁ Type.≟ β₂
...   | no ¬∃β = {! no  !}
...   | yes refl with basic? β₁
...     | no ¬β-ok = no {! no  !}
...     | yes β-ok = yes (Unit , Store r₁ ∙ (η₁ ∪ η₂) , t-store rule₁ rule₂)
synthesize? Γ (e₁ ≔ e₂) | yes (τ₁ , η₁ , rule₁) | yes (τ₂ , η₂ , rule₂) = no {! no  !}

-- FIXME: is this ok?
synthesize? Γ (run r e) = no λ{ (τ , η , rule) → run-synthesize-uninhabited rule }

synthesize? Γ (adr a) with lookup? Γ a
... | no ¬∃ = no {! no  !} -- λ{ (τ , η , t-var ∋x) → ¬∃ (τ , ∋x) }
... | yes (Ref r β , ∋a) = yes (Ref r β , ∅ , t-adr ∋a)
... | yes (τ , ∋a) = no {! no  !}

synthesize? Γ (mem r μ e) with synthesize? (Γ ++ ⌈ μ ⌉ r) e
... | no ¬∃ = no {! no  !}
... | yes (τ , η , rule) with Mutate r ⊆? η
...   | no ¬r⊆η = no {! no  !}
...   | yes r⊆η = yes (τ , η , t-mem r⊆η rule)


synthesize : (Γ : Context) → (e : Expression) → String ⊎ Mono × Effect
synthesize Γ e with synthesize? Γ e
... | yes (τ , η , _) = right (τ , η)
... | no _ = wrong "Type error"
