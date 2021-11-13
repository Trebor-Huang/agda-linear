module Normalize where

open import Types
open import Pattern
open import Linear
open import Canonical

-- We have a little bit of coherence problem that needs to be remedied.
data _≡_ {A : Set} : A -> A -> Set where
    refl : ∀ {a} -> a ≡ a

{-# BUILTIN EQUALITY _≡_ #-}

-- First the non-mutually-recursive functions. The names should be evident
forgetΣ : StrictStack -> Stack
forgetΣ ε̂ₛ = εₛ
forgetΣ (_∷̂ₛ_ {p = p} Σ _) = (forgetΣ Σ) ∷ₛ p

forgetΓ : ∀ {Σ} -> StrictContext Σ -> Context (forgetΣ Σ)
forgetΓ ε̂ = ε
forgetΓ (Γ ∷̂ α) = forgetΓ Γ ∷ α

forget∋̂ : ∀ {Σ t} -> Σ ∋̂ t -> forgetΣ Σ ∋ t
forget∋̂ (𝕫̂ₛ x) = 𝕫ₛ x
forget∋̂ (𝕤̂ₛ α) = 𝕤ₛ forget∋̂ α

forget⊎̂ : ∀ {Σ} {Γ₁ Γ₂ Γ₃ : StrictContext Σ}
    -> Γ₁ ⊎̂ Γ₂ ≅̂ Γ₃ -> forgetΓ Γ₁ ⊎̅ forgetΓ Γ₂ ≅̅ forgetΓ Γ₃
forget⊎̂ ⊎̂ε = ⊎ε
forget⊎̂ (u ⊎̂∷ v) = forget⊎̂ u ⊎∷ v

-- Two little commutation lemmas.
commute-□-Γ : ∀ Σ -> forgetΓ (□̂ Σ) ≡ □̅ (forgetΣ Σ)
commute-□-Γ ε̂ₛ = refl
commute-□-Γ (Σ ∷̂ₛ x) rewrite commute-□-Γ Σ = refl

commute-■∋-Γ : ∀ {Σ t} (v : Σ ∋̂ t) ->  forgetΓ (■̂∋ v) ≡ ■∋ (forget∋̂ v)
commute-■∋-Γ {Σ = Σ ∷̂ₛ _} (𝕫̂ₛ _) rewrite commute-□-Γ Σ = refl
commute-■∋-Γ (𝕤̂ₛ v) rewrite commute-■∋-Γ v = refl

-- Next, the four inductive definitions require mutual recursion.
forget⊨ : ∀ {Σ} {Γ : StrictContext Σ} {j} -> Γ ⊨ j -> (forgetΓ Γ) ⊢ j
forget⊨̅ : ∀ {Σ Σ'} {Γ : StrictContext Σ} -> Γ ⊨̅ Σ' -> (forgetΓ Γ) ⊢̅ (forgetΣ Σ')
forget⊨ₚ : ∀ {Σ t} {p : Pattern t} {α : $̸ p} {Γ : StrictContext Σ}
    -> Γ ⊨ₚ α -> (forgetΓ Γ) ⊢ₚ p
forget⊨ₚₛ# : ∀ {Σ t} {ps : Patterns t} {α̅ : $̸ₚₛ ps} {Γ : StrictContext Σ}
    -> Γ ʻ α̅ ⊨ₚₛ# -> (forgetΓ Γ) ʻ ps ⊢ₚₛ #

forget⊨ (p̃ ⟦ σ ⟧⁺) = cons (forget⊨ₚ σ)
forget⊨ (p̃ ⟦ σ ⟧⁻) = cons (forget⊨ₚ σ)
forget⊨ (case⁺ p̃s tₚₛ c) = case+of (forget⊨ₚₛ# tₚₛ) c
forget⊨ (case⁻ p̃s tₚₛ c) = case-of (forget⊨ₚₛ# tₚₛ) c
forget⊨ ((v ·⁺ t) r) = (coerced-var⁺ · forget⊨ t) (forget⊎̂ r)
    where  -- Use `where` to make the types easier to read.
        coerced-var⁺ : forgetΓ (■̂∋ v) ⊢ :- ● _
        coerced-var⁺ rewrite commute-■∋-Γ v = var (forget∋̂ v)
forget⊨ ((t ·⁻ v) r) = (forget⊨ t · coerced-var⁻) (forget⊎̂ r)
    where
        coerced-var⁻ : forgetΓ (■̂∋ v) ⊢ :- ○ _
        coerced-var⁻ rewrite commute-■∋-Γ v = var (forget∋̂ v)

forget⊨̅ (⊨ε _) = coerce (⊢ε _)
    where
        coerce : ∀ {Σ} -> □̅ (forgetΣ Σ) ⊢̅ forgetΣ ε̂ₛ -> forgetΓ (□̂ Σ) ⊢̅ forgetΣ ε̂ₛ
        coerce {Σ} t rewrite commute-□-Γ Σ = t
forget⊨̅ (⊨∷ t̅ tₚ u) = (forget⊨̅ t̅ ⊢∷ forget⊨ₚ tₚ) (forget⊎̂ u)

forget⊨ₚ (⊨⟨ tₚ , sₚ ⟩ x) = ⊢⟨ forget⊨ₚ tₚ , forget⊨ₚ sₚ ⟩ (forget⊎̂ x)
forget⊨ₚ (⊨ϖ₁ tₚ) = ⊢ϖ₁ (forget⊨ₚ tₚ)
forget⊨ₚ (⊨ϖ₂ tₚ) = ⊢ϖ₂ (forget⊨ₚ tₚ)
forget⊨ₚ (⊨⟪ tₚ , sₚ ⟫ x) = ⊢⟪ forget⊨ₚ tₚ , forget⊨ₚ sₚ ⟫ (forget⊎̂ x)
forget⊨ₚ (⊨π₁ tₚ) = ⊢π₁ (forget⊨ₚ tₚ)
forget⊨ₚ (⊨π₂ tₚ) = ⊢π₂ (forget⊨ₚ tₚ)
forget⊨ₚ {Σ = Σ} ⊨*̂ rewrite commute-□-Γ Σ = ⊢*̂
forget⊨ₚ {Σ = Σ} ⊨*̬ rewrite commute-□-Γ Σ = ⊢*̬
forget⊨ₚ (⊨⇑ t) = ⊢⇑ (forget⊨ t)
forget⊨ₚ (⊨⇓ t) = ⊢⇓ (forget⊨ t)
forget⊨ₚ (⊨●⁺ t) = ⊢●⁺ (forget⊨ t)
forget⊨ₚ (⊨●⁻ t) = ⊢●⁻ (forget⊨ t)

forget⊨ₚₛ# ⊨εₚₛ = ⊢εₚₛ
forget⊨ₚₛ# (⊨∷ₚₛ t tₚₛ) = ⊢∷ₚₛ (forget⊨ t) (forget⊨ₚₛ# tₚₛ)
