module Canonical where
-- Defines the normal forms.
-- Zeilberger defines a much stricter version of canonical forms than usual.
-- For example, the term (x : A ⊗ B) in the context (x:A ⊗ B) is not canonical.
-- Because A ⊗ B is a positive type, and can be decomposed as ⟨ x , y ⟩.
-- If you normalize it, you get (ignoring how A and B can be normalized):
--      x:A, y:B ⊢ ⟨ x , y ⟩ : A ⊗ B.
-- See how even the variables in the context may decay and split.
open import Types
open import Pattern
open import Linear

-- We start with defining "strict" contexts.
-- Zeilberger calls this simple contexts, while the normal contexts are called complex.
infixl 6 _∷̂_ _∷̂ₛ_

data StrictStack : Set where
    ε̂ₛ : StrictStack
    _∷̂ₛ_ : ∀ {t} {p : Pattern t} -> StrictStack -> $̸ p -> StrictStack

data StrictContext : StrictStack -> Set where
    ε̂ : StrictContext ε̂ₛ
    _∷̂_ : ∀ {Σ t} {p : Pattern t} {α : $̸ p}
        -> StrictContext Σ -> Occur p -> StrictContext (Σ ∷̂ₛ α)

infix 5 _⊨_ _⊨̅_ _⊨ₚ_ _ʻ_⊨ₚₛ#

-- Extend deepness to patterns
data $̸ₚₛ : ∀ {t} -> Patterns t -> Set where
    $̸ε : ∀ {t} -> $̸ₚₛ {t} εₚ
    $̸∷ : ∀ {t p} {ps : Patterns t} -> $̸ p -> $̸ₚₛ ps -> $̸ₚₛ (p ∷ₚ ps)

■̂ : ∀ Σ -> StrictContext Σ
■̂ ε̂ₛ = ε̂
■̂ (_ ∷̂ₛ _) = (■̂ _) ∷̂ ■ _

□̂ : ∀ Σ -> StrictContext Σ
□̂ ε̂ₛ = ε̂
□̂ (_ ∷̂ₛ _) = (□̂ _) ∷̂ □ _

infix 6 _∋̂_
data _∋̂_ : StrictStack -> T -> Set where
    𝕫̂ₛ : ∀ {t t' Σ} {p : Pattern t'} {α : $̸ p} -> p ∋ₚ t -> (Σ ∷̂ₛ α) ∋̂ t
    𝕤̂ₛ_ : ∀ {t t' Σ} {p : Pattern t'} {α : $̸ p} -> Σ ∋̂ t -> (Σ ∷̂ₛ α) ∋̂ t

■̂∋ : ∀ {Σ t} -> Σ ∋̂ t -> StrictContext Σ
■̂∋ (𝕫̂ₛ x) = □̂ _ ∷̂ (■∋ₚ x)
■̂∋ (𝕤̂ₛ α) = (■̂∋ α) ∷̂ (□ _)

data _⊎̂_≅̂_ : ∀ {Σ} -> StrictContext Σ -> StrictContext Σ -> StrictContext Σ -> Set where
    ⊎̂ε : ε̂ ⊎̂ ε̂ ≅̂ ε̂
    _⊎̂∷_ : ∀ {t} {p : Pattern t} {α : $̸ p} {Δ₁ Δ₂ Δ₃ : Occur p}
        {Σ} {Γ₁ Γ₂ Γ₃ : StrictContext Σ}
        -> Γ₁ ⊎̂ Γ₂ ≅̂ Γ₃ -> Δ₁ ⊎ Δ₂ ≅ Δ₃ -> (Γ₁ ∷̂ Δ₁) ⊎̂ (Γ₂ ∷̂ Δ₂) ≅̂ (_∷̂_ {α = α} Γ₃ Δ₃)

_⊎̂_ : ∀ {Σ} -> (Γ₁ Γ₂ : StrictContext Σ) -> Maybe (Exists _ \Γ -> Γ₁ ⊎̂ Γ₂ ≅̂ Γ)
ε̂ ⊎̂ ε̂ = Just (exists ε̂ ⊎̂ε)
(Γ₁ ∷̂ α₁) ⊎̂ (Γ₂ ∷̂ α₂) = ⦇ (pair² _∷̂_ _⊎̂∷_) (Γ₁ ⊎̂ Γ₂) (α₁ ⊎ α₂) ⦈

data _⊨_ : ∀ {Σ} -> StrictContext Σ -> J -> Set
data _⊨̅_ : ∀ {Σ} -> StrictContext Σ -> StrictStack -> Set
data _⊨ₚ_ : ∀ {Σ t} {p : Pattern t} -> StrictContext Σ -> $̸ p -> Set
data _ʻ_⊨ₚₛ# : ∀ {Σ t} {ps : Patterns t} -> StrictContext Σ -> $̸ₚₛ ps -> Set

data _⊨_ where
    _⟦_⟧⁺ : ∀ {Σ} {Γ : StrictContext Σ} { A : 𝕋 + } {p : Pattern (○ A)}
        -- A positive canonical value is a pattern
        -- whose variables are substituted with other canonical forms.
        -> (p̃ : $̸ p) -> Γ ⊨ₚ p̃ -> Γ ⊨ :- ○ A
    _⟦_⟧⁻ : ∀ {Σ} {Γ : StrictContext Σ} { A : 𝕋 - } {p : Pattern (● A)}
        -- Dual. Negative canonical continuations.
        -> (p̃ : $̸ p) -> Γ ⊨ₚ p̃ -> Γ ⊨ :- ● A
    case⁺ : ∀ {Σ} {Γ : StrictContext Σ} { A : 𝕋 + } {ps : Patterns (○ A)}
        -- A positive continuation is specified
        -- by case analyzing every possible introduction pattern
        -- of the corresponding value that it can take, and
        -- giving an expression (a program) for each case.
        -> (p̃s : $̸ₚₛ ps) -> Γ ʻ p̃s ⊨ₚₛ# -> Covers (○ A) ps -> Γ ⊨ :- ● A
    case⁻ : ∀ {Σ} {Γ : StrictContext Σ} { A : 𝕋 - } {ps : Patterns (● A)}
        -- Dual.
        -> (p̃s : $̸ₚₛ ps) -> Γ ʻ p̃s ⊨ₚₛ# -> Covers (● A) ps -> Γ ⊨ :- ○ A
    _·⁺_ : ∀ {Σ} {Γ Γ' : StrictContext Σ} { A : 𝕋 + }
        -- To create expressions, apply a value to a continuation.
        -> (v : Σ ∋̂ ● A) -> Γ ⊨ :- ○ A
        -> ((■̂∋ v) ⊎̂ Γ ≅̂ Γ') -> Γ' ⊨ #
    _·⁻_ : ∀ {Σ} {Γ Γ' : StrictContext Σ} { A : 𝕋 - }
        -> Γ ⊨ :- ● A -> (v : Σ ∋̂ ○ A)
        -> (Γ ⊎̂ (■̂∋ v) ≅̂ Γ') -> Γ' ⊨ #

-- The rest are just boring.
data _⊨̅_ where
    ⊨ε : ∀ Σ -> (□̂ Σ) ⊨̅ ε̂ₛ
    ⊨∷ : ∀ {Σ Σ'} {Γ₁ Γ₂ Γ₃ : StrictContext Σ'} {t} {p : Pattern t} {α : $̸ p}
        -> Γ₁ ⊨̅ Σ -> Γ₂ ⊨ₚ α -> Γ₁ ⊎̂ Γ₂ ≅̂ Γ₃ -> Γ₃ ⊨̅ (Σ ∷̂ₛ α)

data _⊨ₚ_ where
    ⊨⟨_,_⟩ : ∀ {Σ} {Γ₁ Γ₂ Γ₃ : StrictContext Σ}
        {A⁺ B⁺} {p : Pattern (○ A⁺)} {q : Pattern (○ B⁺)} {α : $̸ p} {β : $̸ q}
        -> Γ₁ ⊨ₚ α -> Γ₂ ⊨ₚ β -> Γ₁ ⊎̂ Γ₂ ≅̂ Γ₃ -> Γ₃ ⊨ₚ $̸⟨ α , β ⟩
    ⊨ϖ₁ : ∀ {Σ} {Γ : StrictContext Σ}
        {A⁺ B⁺} {p : Pattern (○ A⁺)} {α : $̸ p}
        -> Γ ⊨ₚ α -> Γ ⊨ₚ $̸ϖ₁ {B⁺ = B⁺} α
    ⊨ϖ₂ : ∀ {Σ} {Γ : StrictContext Σ}
        {A⁺ B⁺} {p : Pattern (○ B⁺)} {α : $̸ p}
        -> Γ ⊨ₚ α -> Γ ⊨ₚ $̸ϖ₂ {A⁺ = A⁺} α
    ⊨⟪_,_⟫ : ∀ {Σ} {Γ₁ Γ₂ Γ₃ : StrictContext Σ}
        {A⁻ B⁻} {p : Pattern (● A⁻)} {q : Pattern (● B⁻)} {α : $̸ p} {β : $̸ q}
        -> Γ₁ ⊨ₚ α -> Γ₂ ⊨ₚ β -> Γ₁ ⊎̂ Γ₂ ≅̂ Γ₃ -> Γ₃ ⊨ₚ $̸⟪ α , β ⟫
    ⊨π₁ : ∀ {Σ} {Γ : StrictContext Σ}
        {A⁻ B⁻} {p : Pattern (● A⁻)} {α : $̸ p}
        -> Γ ⊨ₚ α -> Γ ⊨ₚ $̸π₁ {B⁻ = B⁻} α
    ⊨π₂ : ∀ {Σ} {Γ : StrictContext Σ}
        {A⁻ B⁻} {p : Pattern (● B⁻)} {α : $̸ p}
        -> Γ ⊨ₚ α -> Γ ⊨ₚ $̸π₂ {A⁻ = A⁻} α
    ⊨*̂ : ∀ {Σ} -> □̂ Σ ⊨ₚ $̸*̂
    ⊨*̬ : ∀ {Σ} -> □̂ Σ ⊨ₚ $̸*̬
    ⊨⇑ : ∀ {Σ} {A⁺} -> (α̅ : Σ ∋̂ (● A⁺)) -> ■̂∋ α̅ ⊨ₚ $̸⇑ {A⁺}
    ⊨⇓ : ∀ {Σ} {A⁻} -> (α̅ : Σ ∋̂ (○ A⁻)) -> ■̂∋ α̅ ⊨ₚ $̸⇓ {A⁻}
    ⊨●⁺ : ∀ {Σ} {A⁺} -> (α̅ : Σ ∋̂ (● A⁺)) -> ■̂∋ α̅ ⊨ₚ $̸●⁺ {A⁺}
    ⊨●⁻ : ∀ {Σ} {A⁻} -> (α̅ : Σ ∋̂ (○ A⁻)) -> ■̂∋ α̅ ⊨ₚ $̸●⁻ {A⁻}

data _ʻ_⊨ₚₛ# where
    ⊨εₚₛ : ∀ {Σ} {Γ : StrictContext Σ} {t} -> Γ ʻ $̸ε {t = t} ⊨ₚₛ#
    ⊨∷ₚₛ : ∀ {Σ} {Γ : StrictContext Σ}
        {t} {p : Pattern t} {p̃ : $̸ p} {ps : Patterns t} {p̃s : $̸ₚₛ ps}
        -> _∷̂_ {α = p̃} Γ (■ p) ⊨ # -> Γ ʻ p̃s ⊨ₚₛ# -> Γ ʻ ($̸∷ p̃ p̃s) ⊨ₚₛ#
