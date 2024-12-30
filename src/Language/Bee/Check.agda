module Language.Bee.Check where

import Data.String as String
import Language.Bee.Syntax.Effect as Effect
import Language.Bee.Syntax.Type as Type

open import Prelude
open import Language.Bee.Syntax
open import Language.Bee.Judgement


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
-- --   ; (yes ⟨ τ , η , rule ⟩) → {!   !}
-- --   }

check-η-τ? : (Γ : Context) → (e : Expression) → (τ : Type) → (η : Effect) → Dec (Γ ⊢ e ⦂ τ ∥ η)
check-τ? : (Γ : Context) → (e : Expression) → (τ : Type) → Dec (∃[ η ] Γ ⊢ e ⦂ τ ∥ η)
check-η? : (Γ : Context) → (e : Expression) → (η : Effect) → Dec (∃[ τ ] Γ ⊢ e ⦂ τ ∥ η)

synthesize? : (Γ : Context) → (e : Expression) → Dec (∃[ τ ] ∃[ η ] Γ ⊢ e ⦂ τ ∥ η)
synthesize?ᴼ : (Γ : Context) → (o : Operation) → Dec (∃[ τ ] ∃[ η ] Γ ⊢ᴼ o ⦂ τ ∥ η)
synthesizeᴸ : (Γ : Context) → (l : Literal) → ∃[ τ ] Γ ⊢ᴸ l ⦂ τ

check-τ? Γ e τ with synthesize? Γ e
... | no ¬p = {! no !}
... | yes ⟨ τ′ , η , rule ⟩ with τ′ Type.≟ τ
...   | no ¬p = {! no !}
...   | yes refl = yes ⟨ η , rule ⟩

check-η? Γ e η with synthesize? Γ e
... | no ¬p = {! no !}
... | yes ⟨ τ , η′ , rule ⟩ with η′ Effect.⊆? η
...   | no ¬p = {! no !}
...   | yes p = yes ⟨ τ , {! goes wrong here, because η′ ⊆ η and not ≢ !} ⟩

-- inherit? Γ e τ η with synthesize? Γ e
-- ... | no ¬p = {!   !}
-- ... | yes ⟨ τ′ , η′ , rule ⟩ with τ′ Type.≟ τ | η′ Effect.≟ η
-- ...   | no ¬p | no ¬q = {! no !}
-- ...   | no ¬p | yes q = {! no !}
-- ...   | yes p | no ¬q = {! no !}
-- ...   | yes refl | yes refl = yes rule

synthesizeᴸ Γ (word s w _) = ⟨ Word s w , l-word ⟩
synthesizeᴸ Γ True = ⟨ Bool , l-true ⟩
synthesizeᴸ Γ False = ⟨ Bool , l-false ⟩
synthesizeᴸ Γ ⟨⟩ = ⟨ Unit , l-unit ⟩


synthesize?ᴼ Γ (alloc h e) with synthesize? Γ e
... | no ¬∃ = no {! no !}
... | yes ⟨ β , η , rule ⟩ with basic? β
...   | no ¬β-ok = no {! no !}
...   | yes β-ok = yes ⟨ Ref h β {β-ok}, Alloc h ∙ η , o-alloc rule ⟩

synthesize?ᴼ Γ (load e₁) with synthesize? Γ e₁
... | no ¬∃ = no {! no !}
... | yes ⟨ Ref h₁ β₁ , η₁ , rule₁ ⟩ with basic? β₁
...   | no ¬β₁-ok = no {! no !}
...   | yes β₁-ok = yes ⟨ β₁ , Load h₁ ∙ η₁ , o-load rule₁ ⟩
synthesize?ᴼ Γ (load e₁)  | yes ⟨ τ , η , rule ⟩ = {! no  !}

synthesize?ᴼ Γ (store e₁ e₂) with synthesize? Γ e₁ | synthesize? Γ e₂
... | no ¬∃₁ | no ¬∃₂ = no {! no  !}
... | no ¬∃₁ | yes ∃₂ = no {! no  !}
... | yes ∃₁ | no ¬∃₂ = no {! no  !}
... | yes ⟨ Ref h₁ β₁ , η₁ , rule₁ ⟩ | yes ⟨ β₂ , η₂ , rule₂ ⟩ with β₁ Type.≟ β₂
...   | no ¬∃β = {! no  !}
...   | yes refl with basic? β₁
...     | no ¬β-ok = no {! no  !}
...     | yes β-ok = yes ⟨ Unit , Store h₁ ∙ (η₁ ∪ η₂) , o-store rule₁ rule₂ ⟩
synthesize?ᴼ Γ (store e₁ e₂) | yes ⟨ τ₁ , η₁ , rule₁ ⟩ | yes ⟨ τ₂ , η₂ , rule₂ ⟩ = {! no  !}

synthesize?ᴼ Γ (run h e) with check-η? Γ e (Mutate h)
... | yes ⟨ τ , rule ⟩ = yes ⟨ τ , {!  !} , o-run {!   !} {!   !} ⟩ -- ⟨ τ , η ＼ Mutate {!   !} , t-run {! Muth⊆η  !} rule ⟩
... | no ¬∃ = no {! no  !}

-- synthesize?ᴼ Γ panic = yes ⟨ {! some-τ  !} , Panic ∙ ∅ , o-panic ⟩
synthesize?ᴼ Γ panic = no λ x → {!   !}

synthesize?ᴼ Γ (calc f e₁ e₂) = {!   !}
synthesize?ᴼ Γ (comp f e₁ e₂) = {!   !}


-- apply?ᴼ :
--   (Γ : Context) →
--   (o : Operation) →
--   {e⁺ : List Expression} →
--   (τ⁺ : List Type) →
--   {all : All (λ { ⟨ eᵢ , τᵢ ⟩ → ∃[ ηᵢ ] Γ ⊢ eᵢ ⦂ τᵢ ∥ ηᵢ }) (zip e⁺ τ⁺)} →
--   -----------------------------------------------------------------
--   Dec (∃[ τ ] ∃[ η ] Γ ⊢ opr o ◂ e⁺ ⦂ τ ∥ η)
-- apply?ᴼ Γ alloc [ β ] with basic? β
-- ... | yes β-ok = yes ⟨ Ref {!   !} β {{β-ok}} , Alloc {!   !} ∙ ∅ , t-app (t-opr (o-alloc {{β-ok}})) {!   !} ⟩
-- ... | no ¬β-ok = no {!   !}
-- apply?ᴼ Γ load [ Ref h β ] with basic? β
-- ... | yes β-ok = yes {!   !}
-- ... | no ¬β-ok = no {!   !}
-- apply?ᴼ Γ store [ Ref h β₁ , β₂ ] with β₁ Type.≟ β₂
-- ... | yes β-ok = yes {!   !}
-- ... | no ¬β-ok = no {!   !}
-- apply?ᴼ Γ panic [] = {!   !}
-- -- apply?ᴼ Γ (calc _) = ⟨ {!   !} , {!   !} ⟩
-- -- apply?ᴼ Γ (comp _) = ⟨ {!   !} , {!   !} ⟩

-- Note: all `yes` cases prove soundness, all `no` cases completeness
-- synthesize? : (Γ : Context) → (e : Expression) → Dec (∃[ τ ] ∃[ η ] Γ ⊢ e ⦂ τ ∥ η)
synthesize? Γ (` x) with lookup? Γ x
... | yes ⟨ τ , ∋x ⟩ = yes ⟨ τ , ∅ , t-var ∋x ⟩
... | no  ¬∃ = no λ{ ⟨ τ , η , t-var ∋x ⟩ → ¬∃ ⟨ τ , ∋x ⟩ }
synthesize? Γ (e ◂ e⁺) with synthesize? Γ e
... | yes ⟨ τ⁺ ⟨ η₀ ⟩→ τ₀ , η , rule ⟩ with all? (λ {⟨ eᵢ , τᵢ ⟩ → synthesize? Γ eᵢ}) (zip e⁺ τ⁺)
...   | yes p = yes ⟨ τ₀ , η ∪ η₀ ∪ {!   !} , t-app rule {!   !} ⟩
...   | no ¬p = no {! no  !}
synthesize? Γ (lit l) with synthesizeᴸ Γ l
... | ⟨ τ , l-rule ⟩ = yes ⟨ τ , ∅ , t-lit l-rule ⟩
synthesize? Γ (opr o) with synthesize?ᴼ Γ o
... | yes ⟨ τ , η , o-rule ⟩ = yes ⟨ τ , η , t-opr o-rule ⟩
... | no ¬∃ = {! no  !}
synthesize? Γ (val x `= e ⨾ e₁) = {!   !}
synthesize? Γ (`if e₀ then e₁ else e₂) with synthesize? Γ e₀ | synthesize? Γ e₁ | synthesize? Γ e₂
... | yes ⟨ Bool , η₀ , rule₀ ⟩ | yes ⟨ τ₁ , η₁ , rule₁ ⟩ | yes ⟨ τ₂ , η₂ , rule₂ ⟩ with τ₁ Type.≟ τ₂
...   | yes τ₁≡τ₂ rewrite sym τ₁≡τ₂ = yes ⟨ τ₁ , η₀ ∪ η₁ ∪ η₂ , t-cond rule₀ rule₁ rule₂ ⟩
...   | no ¬τ₁≡τ₂ = no {! no  !}
synthesize? Γ (adr a) = yes ⟨ {! Ref h β  !} , ∅ , t-adr {!   !} ⟩
synthesize? Γ (reg⟨ Θ ⟩ e) with synthesize? (Γ ++ ⌈ Θ ⌉ {!   !}) e
... | yes ⟨ τ , η , rule ⟩ = yes ⟨ τ , η , t-reg {! Muth⊆η  !} rule ⟩
... | no ¬∃ = no {! no  !}

synthesize : (Γ : Context) → (e : Expression) → String ⊎ Type × Effect
synthesize Γ e with synthesize? Γ e
... | yes ⟨ τ , η , _ ⟩ = right ⟨ τ , η ⟩
... | no _ = wrong "Type error"

{-
⟨ ? , ? , ? ⟩
-}
