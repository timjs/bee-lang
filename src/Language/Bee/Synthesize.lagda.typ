```agda
module Language.Bee.Synthesize where

import Data.String as String

open import Prelude
open import Language.Bee.Syntax
open import Language.Bee.Judgement

check-all? : (Γ : Context) → (e : Expression) → (τ : Mono) → (η : Effect) → Dec (Γ ⊢ e ⇐ τ ∥ η)
check-type? : (Γ : Context) → (e : Expression) → (τ : Mono) → Dec (∃[ η ] Γ ⊢ e ⇐ τ ⇒ η)
synthesize? : (Γ : Context) → (e : Expression) → Dec (∃[ τ ] ∃[ η ] Γ ⊢ e ⇒ τ ∥ η)
synthesize⁺? : (Γ : Context) → (e⁺ : List Expression) → Dec (∃[ τ⁺ ] ∃[ η ] Γ ⊢ e⁺ ⇒⁺ τ⁺ ∥ η)
synthesizeᴼ? : (Γ : Context) → (o : Operation) → Dec (∃[ τ ] ∃[ η ] Γ ⊢ᴼ o ⇒ τ ∥ η)
synthesizeᴾ : (Γ : Context) → (p : Primitive) → ∃[ τ ] Γ ⊢ᴾ p ⇒ τ

-- Note: all `yes` cases below prove soundness, all `no` cases completeness


check-all? Γ e τ η with synthesize? Γ e
... | no ¬∃ = no {!   !}
... | yes (τ′ , η′ , rule) with τ′ Type.≟ τ | η′ ⊆? η
...   | no ¬∃₁ | no ¬∃₂ = no {!   !}
...   | yes ∃₁ | no ¬∃₂ = no {!   !}
...   | no ¬∃₁ | yes ∃₂ = no {!   !}
...   | yes τ′≡τ | yes η′⊆η = yes (t-sub rule τ′≡τ η′⊆η)


check-type? Γ e τ with synthesize? Γ e
... | no ¬∃ = no {!   !}
... | yes (τ′ , η , rule) with τ Type.≟ τ′
...   | no ¬∃ = no {!   !}
...   | yes refl = yes (η , t-chk rule refl)


synthesizeᴾ Γ ⟨⟩ = (Unit , l-unit)
synthesizeᴾ Γ True = (Bool , l-true)
synthesizeᴾ Γ False = (Bool , l-false)
synthesizeᴾ Γ (word s w _) = (Word s w , l-word)


synthesizeᴼ? Γ (calc f e₁ e₂) = {! TODO !}
synthesizeᴼ? Γ (comp f e₁ e₂) = {! TODO !}


-- Variables
synthesize? Γ (` x) with lookup? Γ x
... | no ¬∃ = no λ{ (τ , η , t-var ∋x) → ¬∃ (τ , ∋x) }
... | yes (τ , ∋x) = yes (τ , ∅ , t-var ∋x)

-- Functions and binding
synthesize? Γ (e₀ ◂ e⁺) with synthesize⁺? Γ e⁺
... | no ¬∃⁺ = no {!   !}
... | yes (τ⁺ , η⁺ , rule⁺) with lookup-overloaded? Γ τ⁺
...   | no ¬∃ = no {!   !}
...   | yes (x₀ , τ₀ , η₀ , Γ∋x₀) with check-type? Γ e₀ (τ⁺ ⟨ η₀ ⟩→ τ₀)
...     | no ¬≡ = no {!   !}
...     | yes (η , rule) = yes (τ₀ , η ∪ η⁺ ∪ η₀ , t-app rule⁺ Γ∋x₀ rule)

synthesize? Γ (val x₁ `= e₁ ⨾ e₀) with synthesize? Γ e₁
... | no ¬∃₁ = no {!   !}
... | yes (τ₁ , η₁ , rule₁) with synthesize? (Γ , x₁ ⦂ τ₁) e₀
...   | no ¬∃₀ = no {!   !}
...   | yes (τ₀ , η₀ , rule₀) = yes (τ₀ , η₁ ∪ η₀ , t-let rule₁ rule₀)

-- Primitives
synthesize? Γ (prim p) with synthesizeᴾ Γ p
... | (τ , p-rule) = yes (τ , ∅ , t-prim p-rule)

synthesize? Γ (oper o) with synthesizeᴼ? Γ o
... | no ¬∃ = no {!   !}
... | yes (τ , η , o-rule) = yes (τ , η , t-oper o-rule)

synthesize? Γ (`if e₀ then e₁ else e₂) with check-type? Γ e₀ Bool
... | no ¬∃₀ = no {!   !}
... | yes (η₀ , rule₀) with synthesize? Γ e₁ | synthesize? Γ e₂
...   | no ¬∃₁ | no ¬∃₂ = no {!   !}
...   | yes ∃₁ | no ¬∃₂ = no {!   !}
...   | no ¬∃₁ | yes ∃₂ = no {!   !}
...   | yes (τ₁ , η₁ , rule₁) | yes (τ₂ , η₂ , rule₂) with τ₁ Type.≟ τ₂
...     | no ¬τ₁≡τ₂ = no {!   !}
...     | yes refl = yes (τ₁ , η₀ ∪ η₁ ∪ η₂ , t-if rule₀ rule₁ rule₂)

-- Optionals
synthesize? Γ (None τ) = yes (τ `? , ∅ , t-none)

synthesize? Γ (Some e) with synthesize? Γ e
... | no ¬∃ = no {!   !}
... | yes (τ , η , rule) = yes (τ `? , η , t-some rule)

synthesize? Γ (`with x₀ ← e₀ else e₁ ⨾ e₂) with synthesize? Γ e₀
... | no ¬∃ = no {!   !}
... | yes (τ₀ `? , η₀ , rule₀) with synthesize? Γ e₁ | synthesize? (Γ , x₀ ⦂ τ₀) e₂
...   | no ¬∃₁ | no ¬∃₂ = no {!   !}
...   | yes ∃₁ | no ¬∃₂ = no {!   !}
...   | no ¬∃₁ | yes ∃₂ = no {!   !}
...   | yes (τ₁ , η₁ , rule₁) | yes (τ₂ , η₂ , rule₂) with τ₁ Type.≟ τ₂
...     | no ¬∃ = no {!   !}
...     | yes refl = yes (τ₁ , η₀ ∪ η₁ ∪ η₂ , t-with rule₀ rule₁ rule₂)
synthesize? Γ (`with x₀ ← e₀ else e₁ ⨾ e₂) | yes (τ₀ , η₀ , rule₀) = no {!   !}

-- References
synthesize? Γ (new r₁ e₁) with synthesize? Γ e₁
... | no ¬∃₁ = no {!   !}
... | yes (β₁ , η₁ , rule₁) with basic? β₁
...   | no ¬β₁-ok = no {!   !}
...   | yes β₁-ok = yes (Ref r₁ β₁ {β₁-ok}, Alloc r₁ ∙ η₁ , t-new rule₁ {β₁-ok})

synthesize? Γ (e₁ !) with synthesize? Γ e₁
... | no ¬∃ = no {!   !}
... | yes (Ref r₁ β₁ , η₁ , rule₁) with basic? β₁
...   | no ¬β₁-ok = no {!   !}
...   | yes β₁-ok = yes (β₁ , Load r₁ ∙ η₁ , t-load rule₁)
synthesize? Γ (e₁ !) | yes (τ₁ , η₁ , rule₁) = no {!   !}

synthesize? Γ (e₁ ≔ e₂) with synthesize? Γ e₁ | synthesize? Γ e₂
... | no ¬∃₁ | no ¬∃₂ = no {!   !}
... | no ¬∃₁ | yes ∃₂ = no {!   !}
... | yes ∃₁ | no ¬∃₂ = no {!   !}
... | yes (Ref r₁ β₁ , η₁ , rule₁) | yes (β₂ , η₂ , rule₂) with β₁ Type.≟ β₂
...   | no ¬∃β = no {!   !}
...   | yes refl with basic? β₁
...     | no ¬β-ok = no {!   !}
...     | yes β-ok = yes (Unit , Store r₁ ∙ (η₁ ∪ η₂) , t-store rule₁ rule₂)
synthesize? Γ (e₁ ≔ e₂) | yes (τ₁ , η₁ , rule₁) | yes (τ₂ , η₂ , rule₂) = no {!   !}

-- FIXME: is this ok?
synthesize? Γ (run r e) with synthesize? Γ e
... | no ¬∃ = no {!   !}
... | yes (τ , η , rule) with r ∉? free Γ
...   | no ¬r∉Γ = no {!   !}
...   | yes r∉Γ = yes ( τ , η ＼ Mutate r , t-run rule r∉Γ)

synthesize? Γ (adr a) with lookup? Γ a
... | no ¬∃ = no {!   !} -- λ{ (τ , η , t-var ∋x) → ¬∃ (τ , ∋x) }
... | yes (Ref r β , ∋a) = yes (Ref r β , ∅ , t-adr ∋a)
... | yes (τ , ∋a) = no {!   !}

synthesize? Γ (mem r μ e) with synthesize? (Γ ++ ⌈ μ ⌉∙ r) e
... | no ¬∃ = no {!   !}
... | yes (τ , η , rule) with Mutate r ⊆? η
...   | no ¬r⊆η = no {!   !}
...   | yes r⊆η = yes (τ , η , t-mem r⊆η rule)


synthesize⁺? Γ []
  = yes ([] , ∅ , s-nil)
synthesize⁺? Γ (e₀ ∷ e⁺) with synthesize? Γ e₀
... | no ¬∃₀ = no {!   !}
... | yes (τ₀ , η₀ , rule₀) with synthesize⁺? Γ e⁺
...   | no ¬∃⁺ = no {!   !}
...   | yes (τ⁺ , η⁺ , rule⁺) = yes (τ₀ ∷ τ⁺ , η₀ ∪ η⁺ , s-cons rule₀ rule⁺)


synthesize : (Γ : Context) → (e : Expression) → String ⊎ Mono × Effect
synthesize Γ e with synthesize? Γ e
... | yes (τ , η , _) = right (τ , η)
... | no _ = wrong "Type error"
```
