module Linear where

open import Types
open import Pattern
-- We start to implement contexts and terms.
-- Since in our syntax the only binding site is pattern matching,
-- Contexts are made up of the patterns.
-- Every time we go into a pattern matching clause, we push the pattern
-- onto the context. Just like how each time we go into a λ, we push
-- a variable onto the context.

-- Stack is a list of patterns; Context additionally records occurrences.
infixr 6 _∷_ _∷ₛ_

data Stack : Set where
    εₛ : Stack
    _∷ₛ_ : ∀ {t} -> Stack -> Pattern t -> Stack

data Context : Stack -> Set where
    ε : Context εₛ
    _∷_ : ∀ {t} {p : Pattern t} {Σ} -> Context Σ -> Occur p -> Context (Σ ∷ₛ p)

-- Extend Occurrences to Contexts
■̅ : ∀ Σ -> Context Σ
■̅ εₛ = ε
■̅ (Σ ∷ₛ p) = ■̅ Σ ∷ ■ p

□̅ : ∀ Σ -> Context Σ
□̅ εₛ = ε
□̅ (Σ ∷ₛ p) = □̅ Σ ∷ □ p

-- Extend dBI to Contexts
data _∋_ : Stack -> T -> Set where
    𝕫ₛ : ∀ {t t' Σ} {p : Pattern t'} -> p ∋ₚ t -> (Σ ∷ₛ p) ∋ t
    𝕤ₛ_ : ∀ {t t' Σ} {p : Pattern t'} -> Σ ∋ t -> (Σ ∷ₛ p) ∋ t

■∋ : ∀ {Σ t} -> Σ ∋ t -> Context Σ
■∋ (𝕫ₛ α) = (□̅ _) ∷ ■∋ₚ α
■∋ (𝕤ₛ α̅) = (■∋ α̅) ∷ (□ _)

-- If your font can't display it, it is ⊎ with an overline.
data _⊎̅_≅̅_ : ∀ {s} -> Context s -> Context s -> Context s -> Set where
    ⊎ε : ε ⊎̅ ε ≅̅ ε
    _⊎∷_ : ∀ {t} {p : Pattern t} {Δ₁ Δ₂ Δ₃ : Occur p} {Σ} {Γ₁ Γ₂ Γ₃ : Context Σ}
        -> Γ₁ ⊎̅ Γ₂ ≅̅ Γ₃ -> Δ₁ ⊎ Δ₂ ≅ Δ₃ -> (Γ₁ ∷ Δ₁) ⊎̅ (Γ₂ ∷ Δ₂) ≅̅ (Γ₃ ∷ Δ₃)

_⊎̅_ : ∀ {Σ} -> (Γ₁ Γ₂ : Context Σ) -> Maybe (Exists _ \Γ -> Γ₁ ⊎̅ Γ₂ ≅̅ Γ)
ε ⊎̅ ε = Just (exists ε ⊎ε)
(Γ₁ ∷ Δ₁) ⊎̅ (Γ₂ ∷ Δ₂) = ⦇ (pair² _∷_ _⊎∷_) (Γ₁ ⊎̅ Γ₂) (Δ₁ ⊎ Δ₂) ⦈

infix 5 _⊢_ _⊢̅_ _⊢ₚ_ _ʻ_⊢ₚₛ_

-- FOUR interleaving inductive types
data _⊢_ : ∀ {Σ} -> Context Σ -> J -> Set
-- The usual judgement
data _⊢̅_ : ∀ {Σ} -> Context Σ -> Stack -> Set
data _⊢ₚ_ : ∀ {Σ t} -> Context Σ -> Pattern t -> Set
-- The above two judgements makes it more convenient to reason
-- about a set of judgements.
data _ʻ_⊢ₚₛ_ : ∀ {Σ t} -> Context Σ -> Patterns t -> J -> Set
-- This collects a bunch of judgements for pattern matching clauses
-- and makes a judgement about the whole pattern matching term.
-- ʻ means that the context on the left is shared.

data _⊢_ where
    var : ∀ {Σ t} (α̅ : Σ ∋ t) -> ■∋ α̅ ⊢ :- t  -- A single variable
    _·_ : ∀ {Σ} {Γ₁ Γ₂ Γ₃ : Context Σ} {p} {A : 𝕋 p}
        -- Applying a term to its continuation.
        -> Γ₁ ⊢ :- (● A) -> Γ₂ ⊢ :- (○ A) -> Γ₁ ⊎̅ Γ₂ ≅̅ Γ₃ -> Γ₃ ⊢ #
    case+of : ∀ {Σ} {Γ : Context Σ} { A⁺ : 𝕋 + } {ps : Patterns (○ A⁺)}
        -- The crux of focused type theories.
        -- To construct a continuation to a positive type,
        -- you just construct an expression for every pattern of that type.
        -> Γ ʻ ps ⊢ₚₛ # -> Covers (○ A⁺) ps -> Γ ⊢ :- (● A⁺)
    case-of : ∀ {Σ} {Γ : Context Σ} { A⁻ : 𝕋 - } {ps : Patterns (● A⁻)}
        -- Dual.
        -> Γ ʻ ps ⊢ₚₛ # -> Covers (● A⁻) ps -> Γ ⊢ :- (○ A⁻)
    case_of : ∀ {Σ t} {Γ₁ Γ₂ Γ₃ : Context Σ} {ps : Patterns t} {j}
        -- Case splitting on an arbitrary term.
        -- This demonstrates the semantics of _ʻ_⊢ₚₛ_.
        -> Γ₁ ⊢ :- t -> Γ₂ ʻ ps ⊢ₚₛ j -> Covers t ps -> Γ₁ ⊎̅ Γ₂ ≅̅ Γ₃ -> Γ₃ ⊢ j
    _⦅_⦆ : ∀ {Σ Σ'} {Γ' : Context Σ'} {j}
        -- Composition of two judgements.
        -> (■̅ Σ) ⊢ j -> Γ' ⊢̅ Σ -> Γ' ⊢ j

infixl 9 _⦅_⦆
infixl 8 _·_

data _⊢̅_ where  -- Boring. We just combine judgments together.
    ⊢ε : ∀ Σ -> (□̅ Σ) ⊢̅ εₛ
    _⊢∷_ : ∀ {Σ Σ'} {Γ₁ Γ₂ Γ₃ : Context Σ'} {t} {p : Pattern t}
        -> Γ₁ ⊢̅ Σ -> Γ₂ ⊢ₚ p -> Γ₁ ⊎̅ Γ₂ ≅̅ Γ₃ -> Γ₃ ⊢̅ (Σ ∷ₛ p)

data _⊢ₚ_ where  -- This mirrors the structure of patterns.
    ⊢⟨_,_⟩ : ∀ {Σ} {Γ₁ Γ₂ Γ₃ : Context Σ} {A⁺ B⁺} {p : Pattern (○ A⁺)} {q : Pattern (○ B⁺)}
        -> Γ₁ ⊢ₚ p -> Γ₂ ⊢ₚ q -> Γ₁ ⊎̅ Γ₂ ≅̅ Γ₃ -> Γ₃ ⊢ₚ ⟨ p , q ⟩
    ⊢ϖ₁ : ∀ {Σ} {Γ₁ Γ₂ Γ₃ : Context Σ} {A⁺ B⁺} {p : Pattern (○ A⁺)} {q : Pattern (○ A⁺ ⊕ B⁺)}
        -> Γ₁ ⊢ₚ p -> Γ₁ ⊎̅ Γ₂ ≅̅ Γ₃ -> Γ₃ ⊢ₚ ϖ₁ {B⁺ = B⁺} p
    ⊢ϖ₂ : ∀ {Σ} {Γ₁ Γ₂ Γ₃ : Context Σ} {A⁺ B⁺} {p : Pattern (○ B⁺)} {q : Pattern (○ A⁺ ⊕ B⁺)}
        -> Γ₂ ⊢ₚ p -> Γ₁ ⊎̅ Γ₂ ≅̅ Γ₃ -> Γ₃ ⊢ₚ ϖ₂ {A⁺ = A⁺} p
    ⊢⟪_,_⟫ : ∀ {Σ} {Γ₁ Γ₂ Γ₃ : Context Σ} {A⁻ B⁻} {p : Pattern (● A⁻)} {q : Pattern (● B⁻)}
        -> Γ₁ ⊢ₚ p -> Γ₂ ⊢ₚ q -> Γ₁ ⊎̅ Γ₂ ≅̅ Γ₃ -> Γ₃ ⊢ₚ ⟪ p , q ⟫
    ⊢π₁ : ∀ {Σ} {Γ₁ Γ₂ Γ₃ : Context Σ} {A⁻ B⁻} {p : Pattern (● A⁻)} {q : Pattern (● A⁻ & B⁻)}
        -> Γ₁ ⊢ₚ p -> Γ₁ ⊎̅ Γ₂ ≅̅ Γ₃ -> Γ₂ ⊢ₚ π₁ {B⁻ = B⁻} p
    ⊢π₂ : ∀ {Σ} {Γ₁ Γ₂ Γ₃ : Context Σ} {A⁻ B⁻} {p : Pattern (● B⁻)} {q : Pattern (● A⁻ & B⁻)}
        -> Γ₁ ⊢ₚ p -> Γ₁ ⊎̅ Γ₂ ≅̅ Γ₃ -> Γ₂ ⊢ₚ π₂ {A⁻ = A⁻} p
    ⊢*̂ : ∀ {Σ} -> □̅ Σ ⊢ₚ *̂
    ⊢*̬ : ∀ {Σ} -> □̅ Σ ⊢ₚ *̬
    ⊢⇑ : ∀ {Σ} {A⁺} -> (α̅ : Σ ∋ (● A⁺)) -> ■∋ α̅ ⊢ₚ ⇑ A⁺
    ⊢⇓ : ∀ {Σ} {A⁻} -> (α̅ : Σ ∋ (○ A⁻)) -> ■∋ α̅ ⊢ₚ ⇓ A⁻
    ⊢●⁺ : ∀ {Σ} {A⁺} -> (α̅ : Σ ∋ (● A⁺)) -> ■∋ α̅ ⊢ₚ ●⁺ A⁺
    ⊢●⁻ : ∀ {Σ} {A⁻} -> (α̅ : Σ ∋ (○ A⁻)) -> ■∋ α̅ ⊢ₚ ●⁻ A⁻
    ⊢$ : ∀ {Σ} {t} -> (α̅ : Σ ∋ t) -> ■∋ α̅ ⊢ₚ $ t


data _ʻ_⊢ₚₛ_ where
    ⊢εₚₛ : ∀ {Σ} {Γ : Context Σ} {t j} -> Γ ʻ (εₚ {t}) ⊢ₚₛ j
    -- Note that this trivially uses variables in Γ.
    -- So when you pattern match on an empty type, you don't need
    -- to care about linearity!
    ⊢∷ₚₛ : ∀ {Σ} {Γ : Context Σ} {t} {p : Pattern t} {ps j}
        -> Γ ∷ (■ p) ⊢ j -> Γ ʻ ps ⊢ₚₛ j -> Γ ʻ (p ∷ₚ ps) ⊢ₚₛ j

-- Some sanity checks
-- A ⊢ A
id : ∀ {A : 𝕋 +} -> ε ∷ (■$ₒ {○ A}) ⊢ :- ○ A
id = var (𝕫ₛ ~$)

-- Excluded middle is provable! For negative types it's just (A ⅋ ¬ A).
-- Note that if you used the other disjunction ⊕, it becomes unprovable.
pem⁻ : ∀ {A} -> ε ⊢ :- ○ (A ⅋ ¬⁻ A)
pem⁻ = case-of (⊢∷ₚₛ
        ((var (𝕫ₛ ⟪ ~$ ,~⟫) · var (𝕫ₛ ⟪~, ~●⁻ ⟫))
            (⊎ε ⊎∷ ⊎⟪ ⊎$L , ⊎●⁻R ⟫))
        ⊢εₚₛ)
    (☺ proof)
    where
        proof : _
        proof ⟪ _ , ●⁻ _ ⟫ $̸⟪ _ , $̸●⁻ ⟫ = ☹̸𝕫
-- In less cluttered syntax, this is just
-- case-of
--      ⟪ κ, a ⟫ ↦ κ · a
