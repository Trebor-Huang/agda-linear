module Normalize where

open import Types
open import Pattern
open import Linear
open import Canonical

-- We first implement the forgetful functors.

-- We have a little bit of coherence problem that needs to be remedied.
data _≡_ {ℓ} {A : Set ℓ} : A -> A -> Set ℓ where
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
forget⊨ (var⁺ v) rewrite commute-■∋-Γ v = var (forget∋̂ v)
forget⊨ (var⁻ v) rewrite commute-■∋-Γ v = var (forget∋̂ v)
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

-- We now need more tools on equalities
cong : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : (a : A) -> B) {x} {y} -> x ≡ y -> f x ≡ f y
cong f r rewrite r = refl

symm : ∀ {ℓ} {A : Set ℓ} {x y : A} -> x ≡ y -> y ≡ x
symm refl = refl

transp : ∀ {ℓ} {A B : Set ℓ} -> (A ≡ B) -> A -> B
transp refl x = x

-- Now we try to `quote`.
quoteΓ : ∀ {Σ} -> (fΓ : Context (forgetΣ Σ))
    -> Exists _ \Γ -> fΓ ≡ forgetΓ Γ  -- This is just the singleton type in inspect idioms.
quoteΓ {ε̂ₛ} ε = exists ε̂ refl
quoteΓ {Σ ∷̂ₛ p} (fΓ ∷ α) with quoteΓ {Σ} fΓ
... | exists fΓ' eq = exists (fΓ' ∷̂ α) (cong (\fΓ -> fΓ ∷ α) eq)

private
    pl : ∀ {Σ t} {p : Pattern t} -> Context (Σ ∷ₛ p) -> Context Σ
    pl (Γ ∷ _) = Γ

    pr : ∀ {Σ t} {p : Pattern t} -> Context (Σ ∷ₛ p) -> Occur p
    pr (_ ∷ p) = p

quote-□-Γ : ∀ {Σ} {Γ : StrictContext Σ} -> (forgetΓ Γ ≡ □̅ (forgetΣ Σ)) -> Γ ≡ □̂ Σ
quote-□-Γ {ε̂ₛ} {ε̂} refl = refl
quote-□-Γ {Σ ∷̂ₛ p} {Γ ∷̂ p̂} r
    rewrite quote-□-Γ {Σ} {Γ} (cong pl r)
    rewrite cong pr r = refl

quote⊎̅ : ∀ {Σ} {Γ₁ Γ₂ Γ₃ : StrictContext Σ}
    -> (forgetΓ Γ₁) ⊎̅ (forgetΓ Γ₂) ≅̅ (forgetΓ Γ₃)
    -> Γ₁ ⊎̂ Γ₂ ≅̂ Γ₃
quote⊎̅ {ε̂ₛ} {ε̂} {ε̂} {ε̂} ⊎ε = ⊎̂ε
quote⊎̅ {Σ ∷̂ₛ x} {Γ₁ ∷̂ x₁} {Γ₂ ∷̂ x₂} {Γ₃ ∷̂ x₃} (s ⊎∷ s₀) = quote⊎̅ s ⊎̂∷ s₀

quote⊢ : ∀ {Σ} {Γ : StrictContext Σ} {j} -> (forgetΓ Γ) ⊢ j -> Γ ⊨ j
quote⊢̅ : ∀ {Σ Σ'} {Γ : StrictContext Σ} -> (forgetΓ Γ) ⊢̅ (forgetΣ Σ') -> Γ ⊨̅ Σ'
quote⊢ₚ : ∀ {Σ t} {p : Pattern t} {α : $̸ p} {Γ : StrictContext Σ}
    -> (forgetΓ Γ) ⊢ₚ p -> Γ ⊨ₚ α
quote⊢ₚₛ# : ∀ {Σ t} {ps : Patterns t} {α̅ : $̸ₚₛ ps} {Γ : StrictContext Σ}
    -> (forgetΓ Γ) ʻ ps ⊢ₚₛ # -> Γ ʻ α̅ ⊨ₚₛ#

quote⊢ {Γ} {j} t = {!  !}

quote⊢̅ {Σ} {Σ'} {Γ} t̅ with forgetΣ Σ' | forgetΓ Γ
quote⊢̅ {Σ} {Σ'} {Γ} (⊢ε .(forgetΣ Σ)) | εₛ | .(□̅ (forgetΣ Σ)) = {!   !}
quote⊢̅ {Σ} {Σ'} {Γ} ((t̅ ⊢∷ x) x₁) | .(_ ∷ₛ _) | Γf = {!   !}

quote⊢ₚ {Σ} {t} {p} {α} {Γ} tₚ with forgetΓ Γ in eq
quote⊢ₚ {Σ} {○ A ⊗ B} {⟨ p , q ⟩} {$̸⟨ α , β ⟩} {Γ} (⊢⟨_,_⟩ {Γ₁ = Γ₁} {Γ₂ = Γ₂} tₚ sₚ x) | _
    with quoteΓ Γ₁ | quoteΓ Γ₂
... | exists fΓ₁ eq₁ | exists fΓ₂ eq₂
    = ⊨⟨ quote⊢ₚ fp , quote⊢ₚ fq ⟩ (quote⊎̅ fx)
    where
        fp : forgetΓ fΓ₁ ⊢ₚ p
        fp rewrite eq₁ = tₚ
        fq : forgetΓ fΓ₂ ⊢ₚ q
        fq rewrite eq₂ = sₚ
        fx : forgetΓ fΓ₁ ⊎̅ forgetΓ fΓ₂ ≅̅ forgetΓ Γ
        fx rewrite eq₁ rewrite eq₂ rewrite eq = x
quote⊢ₚ {Σ} {○ A ⊕ B} {ϖ₁ p} {$̸ϖ₁ α} {Γ} (⊢ϖ₁ tₚ) | _
    = ⊨ϖ₁ (quote⊢ₚ fp)
    where
        fp : forgetΓ Γ ⊢ₚ p
        fp rewrite eq = tₚ
quote⊢ₚ {Σ} {○ A ⊕ B} {ϖ₂ q} {$̸ϖ₂ β} {Γ} (⊢ϖ₂ sₚ) | _
    = ⊨ϖ₂ (quote⊢ₚ fq)
    where
        fq : forgetΓ Γ ⊢ₚ q
        fq rewrite eq = sₚ
quote⊢ₚ {Σ} {● A ⅋ B} {⟪ p , q ⟫} {$̸⟪ α , β ⟫} {Γ} (⊢⟪_,_⟫ {Γ₁ = Γ₁} {Γ₂ = Γ₂} tₚ sₚ x) | _
    with quoteΓ Γ₁ | quoteΓ Γ₂
... | exists fΓ₁ eq₁ | exists fΓ₂ eq₂
    = ⊨⟪ quote⊢ₚ fp , quote⊢ₚ fq ⟫ (quote⊎̅ fx)
    where
        fp : forgetΓ fΓ₁ ⊢ₚ p
        fp rewrite eq₁ = tₚ
        fq : forgetΓ fΓ₂ ⊢ₚ q
        fq rewrite eq₂ = sₚ
        fx : forgetΓ fΓ₁ ⊎̅ forgetΓ fΓ₂ ≅̅ forgetΓ Γ
        fx rewrite eq₁ rewrite eq₂ rewrite eq = x
quote⊢ₚ {Σ} {● A & B} {π₁ p} {$̸π₁ α} {Γ} (⊢π₁ tₚ) | _
    = ⊨π₁ (quote⊢ₚ fp)
    where
        fp : forgetΓ Γ ⊢ₚ p
        fp rewrite eq = tₚ
quote⊢ₚ {Σ} {● A & B} {π₂ q} {$̸π₂ β} {Γ} (⊢π₂ sₚ) | _
    = ⊨π₂ (quote⊢ₚ fq)
    where
        fq : forgetΓ Γ ⊢ₚ q
        fq rewrite eq = sₚ
quote⊢ₚ {Σ} {○ 𝟙} {.*̂} {$̸*̂} {Γ} ⊢*̂ | .(□̅ (forgetΣ Σ))
    rewrite quote-□-Γ {Γ = Γ} eq = ⊨*̂
quote⊢ₚ {Σ} {● ⊥} {.*̬} {$̸*̬} {Γ} ⊢*̬ | .(□̅ (forgetΣ Σ))
    rewrite quote-□-Γ {Γ = Γ} eq = ⊨*̬
quote⊢ₚ {Σ} {○ ↑ A} {.(⇑ _)} {$̸⇑} {Γ} (⊢⇑ x) | Γf = ⊨⇑ (quote⊢ coerced-x)
    where
        coerced-x : forgetΓ Γ ⊢ :- ● A
        coerced-x rewrite cong (λ Γ → Γ ⊢ :- ● A) eq = x
quote⊢ₚ {Σ} {● ↓ A} {.(⇓ A)} {$̸⇓} {Γ} (⊢⇓ x) | Γf = ⊨⇓ (quote⊢ coerced-x)
    where
        coerced-x : forgetΓ Γ ⊢ :- ○ A
        coerced-x rewrite cong (λ Γ → Γ ⊢ :- ○ A) eq = x
quote⊢ₚ {Σ} {○ ¬⁺ A} {.(●⁺ A)} {$̸●⁺} {Γ} (⊢●⁺ x) | Γf = ⊨●⁺ (quote⊢ coerced-x)
    where
        coerced-x : forgetΓ Γ ⊢ :- ● A
        coerced-x rewrite cong (λ Γ → Γ ⊢ :- ● A) eq = x
quote⊢ₚ {Σ} {● ¬⁻ A} {.(●⁻ A)} {$̸●⁻} {Γ} (⊢●⁻ x) | Γf = ⊨●⁻ (quote⊢ coerced-x)
    where
        coerced-x : forgetΓ Γ ⊢ :- ○ A
        coerced-x rewrite cong (λ Γ → Γ ⊢ :- ○ A) eq = x

quote⊢ₚₛ# {_} {_} {.εₚ} {$̸ε} ⊢εₚₛ = ⊨εₚₛ
quote⊢ₚₛ# {_} {_} {.(_ ∷ₚ _)} {$̸∷ _ _} (⊢∷ₚₛ t t#)
    = ⊨∷ₚₛ (quote⊢ t) (quote⊢ₚₛ# t#)

-- Finally, we prove that forget ∘ quote = id. This proves that normal forms are indeed normal.
-- -} 