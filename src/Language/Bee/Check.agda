module Language.Bee.Check where

open import Prelude
open import Language.Bee.Syntax
open import Language.Bee.Judgement

inherit? : (Γ : Context) → (e : Expression) → (τ : Type) → (η : Effect) → Dec (Γ ⊢ e ⦂ τ ∥ η)
inherit? Γ e τ η = {!   !}

synthesizeᴸ : (Γ : Context) → (l : Literal) → ∃[ τ ] Γ ⊢ᴸ l ⦂ τ
synthesizeᴸ Γ (word s w _) = ⟨ Word s w , l-word ⟩
synthesizeᴸ Γ `true = ⟨ Bool , l-true ⟩
synthesizeᴸ Γ `false = ⟨ Bool , l-false ⟩
synthesizeᴸ Γ ⟨⟩ = ⟨ Unit , l-unit ⟩

synthesizeᴼ : (Γ : Context) → (o : Operation) → ∃[ τ ] Γ ⊢ᴼ o ⦂ τ
synthesizeᴼ Γ o = {!   !}

apply?ᴼ :
  (Γ : Context) →
  (o : Operation) →
  {e⁺ : List Expression} →
  (τ⁺ : List Type) →
  {all : All (λ { ⟨ eᵢ , τᵢ ⟩ → ∃[ ηᵢ ] Γ ⊢ eᵢ ⦂ τᵢ ∥ ηᵢ }) (zip e⁺ τ⁺)} →
  -----------------------------------------------------------------
  Dec (∃[ τ ] ∃[ η ] Γ ⊢ opr o ◂ e⁺ ⦂ τ ∥ η)
apply?ᴼ Γ alloc [ β ] with basic? β
... | yes β-ok = yes ⟨ Ref {!   !} β {{β-ok}} , Alloc {!   !} ∙ ∅ , t-app (t-opr (o-alloc {{β-ok}})) {!   !} ⟩
... | no ¬β-ok = no {!   !}
apply?ᴼ Γ load [ Ref h β ] with basic? β
... | yes β-ok = yes {!   !}
... | no ¬β-ok = no {!   !}
apply?ᴼ Γ store [ Ref h β₁ , β₂ ] with β₁ ≟ β₂
... | yes β-ok = yes {!   !}
... | no ¬β-ok = no {!   !}
apply?ᴼ Γ panic [] = {!   !}
-- apply?ᴼ Γ (calc _) = ⟨ {!   !} , {!   !} ⟩
-- apply?ᴼ Γ (comp _) = ⟨ {!   !} , {!   !} ⟩

-- Note: this proves soundness.
-- To also prove completeness, return `Dec (∃[ τ ] ∃[ η ] Γ ⊢ e ⦂ τ ∥ η)`
synthesize? : (Γ : Context) → (e : Expression) → Dec (∃[ τ ] ∃[ η ] Γ ⊢ e ⦂ τ ∥ η)
synthesize? Γ (` x) with lookup? Γ x
... | yes ⟨ τ , ∋x ⟩ = yes ⟨ τ , ∅ , t-var ∋x ⟩
... | no  ¬∃ = no λ{ ⟨ τ , η , t-var ∋x ⟩ → ¬∃ ⟨ τ , ∋x ⟩ }
synthesize? Γ (e ◂ e⁺) with synthesize? Γ e
... | yes ⟨ τ⁺ ⟨ η₀ ⟩→ τ₀ , η , rule ⟩ with all? (λ {⟨ eᵢ , τᵢ ⟩ → synthesize? Γ eᵢ}) (zip e⁺ τ⁺)
...   | yes p = yes ⟨ τ₀ , η ∪ η₀ ∪ {!   !} , t-app rule {!   !} ⟩
...   | no ¬p = no {!   !}
synthesize? Γ (lit l) with synthesizeᴸ Γ l
... | ⟨ τ , l-rule ⟩ = yes ⟨ τ , ∅ , t-lit l-rule ⟩
synthesize? Γ (opr o) with synthesizeᴼ Γ o
... | ⟨ τ , o-rule ⟩ = yes ⟨ τ , ∅ , t-opr o-rule ⟩
synthesize? Γ (val x `= e ⨾ e₁) = {!   !}
synthesize? Γ (`if e₀ then e₁ else e₂) with synthesize? Γ e₀ | synthesize? Γ e₁ | synthesize? Γ e₂
... | yes ⟨ Bool , η₀ , rule₀ ⟩ | yes ⟨ τ₁ , η₁ , rule₁ ⟩ | yes ⟨ τ₂ , η₂ , rule₂ ⟩ with τ₁ ≟ τ₂
...   | yes τ₁≡τ₂ rewrite sym τ₁≡τ₂ = yes ⟨ τ₁ , η₀ ∪ η₁ ∪ η₂ , t-cond rule₀ rule₁ rule₂ ⟩
...   | no ¬τ₁≡τ₂ = no {!   !}
synthesize? Γ (adr a) = yes ⟨ {! Ref h β  !} , ∅ , {! t-adr  !} ⟩
synthesize? Γ (reg⟨ Θ ⟩ e) with synthesize? (Γ ++ ⌈ Θ ⌉ {!   !}) e
... | yes ⟨ τ , η , rule ⟩ = yes ⟨ τ , η , t-reg {! Muth⊆η  !} rule ⟩
... | no ¬∃ = no {!   !}
synthesize? Γ (run e) with synthesize? Γ e
... | yes ⟨ τ , η , rule ⟩ = yes ⟨ τ , η ＼ Mutate {!   !} , t-run {! Muth⊆η  !} rule ⟩
... | no ¬∃ = no {!   !}

synthesize : (Γ : Context) → (e : Expression) → String ⊎ Type × Effect
synthesize Γ e with synthesize? Γ e
... | yes ⟨ τ , η , _ ⟩ = right ⟨ τ , η ⟩
... | no _ = wrong "Type error"

{-
⟨ ? , ? , ? ⟩
-}
