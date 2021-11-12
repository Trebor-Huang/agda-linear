module Linear where

open import Types
open import Pattern

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

data _∋_ : Stack -> T -> Set where
    𝕫ₛ : ∀ {t t' Σ} {p : Pattern t'} -> p ∋ₚ t -> (Σ ∷ₛ p) ∋ t
    𝕤ₛ_ : ∀ {t t' Σ} {p : Pattern t'} -> Σ ∋ t -> (Σ ∷ₛ p) ∋ t

■∋ : ∀ {Σ t} -> Σ ∋ t -> Context Σ
■∋ (𝕫ₛ α) = (□̅ _) ∷ ■∋ₚ α
■∋ (𝕤ₛ α̅) = (■∋ α̅) ∷ (□ _)

data _⊎̅_≅̅_ : ∀ {s} -> Context s -> Context s -> Context s -> Set where
    ⊎ε : ε ⊎̅ ε ≅̅ ε
    _⊎∷_ : ∀ {t} {p : Pattern t} {Δ₁ Δ₂ Δ₃ : Occur p} {Σ} {Γ₁ Γ₂ Γ₃ : Context Σ}
        -> Γ₁ ⊎̅ Γ₂ ≅̅ Γ₃ -> Δ₁ ⊎ Δ₂ ≅ Δ₃ -> (Γ₁ ∷ Δ₁) ⊎̅ (Γ₂ ∷ Δ₂) ≅̅ (Γ₃ ∷ Δ₃)

_⊎̅_ : ∀ {Σ} -> (Γ₁ Γ₂ : Context Σ) -> Maybe (Exists _ \Γ -> Γ₁ ⊎̅ Γ₂ ≅̅ Γ)
ε ⊎̅ ε = Just (exists ε ⊎ε)
(Γ₁ ∷ Δ₁) ⊎̅ (Γ₂ ∷ Δ₂) = ⦇ (pair² _∷_ _⊎∷_) (Γ₁ ⊎̅ Γ₂) (Δ₁ ⊎ Δ₂) ⦈

infix 5 _⊢_ _⊢̅_ _⊢ₚ_ _ʻ_⊢ₚₛ_

data _⊢_ : ∀ {Σ} -> Context Σ -> J -> Set
data _⊢̅_ : ∀ {Σ} -> Context Σ -> Stack -> Set
data _⊢ₚ_ : ∀ {Σ t} -> Context Σ -> Pattern t -> Set
data _ʻ_⊢ₚₛ_ : ∀ {Σ t} -> Context Σ -> Patterns t -> J -> Set
-- ʻ means that the context on the left is shared.

data _⊢_ where
    var : ∀ {Σ t} (α̅ : Σ ∋ t) -> ■∋ α̅ ⊢ :- t
    _·_ : ∀ {Σ} {Γ₁ Γ₂ Γ₃ : Context Σ} {p} {A : 𝕋 p}
        -> Γ₁ ⊢ :- (● A) -> Γ₂ ⊢ :- (○ A) -> Γ₁ ⊎̅ Γ₂ ≅̅ Γ₃ -> Γ₃ ⊢ #
    case+of : ∀ {Σ} {Γ : Context Σ} { A⁺ : 𝕋 + } {ps : Patterns (○ A⁺)}
        -> Γ ʻ ps ⊢ₚₛ # -> Covers (○ A⁺) ps -> Γ ⊢ :- (● A⁺)
    case-of : ∀ {Σ} {Γ : Context Σ} { A⁻ : 𝕋 - } {ps : Patterns (● A⁻)}
        -> Γ ʻ ps ⊢ₚₛ # -> Covers (● A⁻) ps -> Γ ⊢ :- (○ A⁻)
    case_of : ∀ {Σ t} {Γ₁ Γ₂ Γ₃ : Context Σ} {ps : Patterns t} {j}
        -> Γ₁ ⊢ :- t -> Γ₂ ʻ ps ⊢ₚₛ j -> Covers t ps -> Γ₁ ⊎̅ Γ₂ ≅̅ Γ₃ -> Γ₃ ⊢ j
    _⦅_⦆ : ∀ {Σ Σ'} {Γ' : Context Σ'} {j}
        -> (■̅ Σ) ⊢ j -> Γ' ⊢̅ Σ -> Γ' ⊢ j

infixl 9 _⦅_⦆
infixl 8 _·_

data _⊢̅_ where
    ⊢ε : ∀ Σ -> (□̅ Σ) ⊢̅ εₛ
    _⊢∷_ : ∀ {Σ Σ'} {Γ₁ Γ₂ Γ₃ : Context Σ'} {t} {p : Pattern t}
        -> Γ₁ ⊢̅ Σ -> Γ₂ ⊢ₚ p -> Γ₁ ⊎̅ Γ₂ ≅̅ Γ₃ -> Γ₃ ⊢̅ (Σ ∷ₛ p)

data _⊢ₚ_ where
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
    ⊢εₚₛ : ∀ {Σ t j} -> (□̅ Σ) ʻ (εₚ {t}) ⊢ₚₛ j
    ⊢∷ₚₛ : ∀ {Σ} {Γ₁ Γ₂ Γ₃ : Context Σ} {t} {p : Pattern t} {ps j}
        -> Γ₁ ⊎̅ Γ₂ ≅̅ Γ₃
        -> Γ₁ ∷ (■ p) ⊢ j -> Γ₂ ʻ ps ⊢ₚₛ j -> Γ₃ ʻ (p ∷ₚ ps) ⊢ₚₛ j

-- Some sanity checks
id : ∀ {A : 𝕋 +} -> ε ∷ (■$ₒ {○ A}) ⊢ :- ○ A
id = var (𝕫ₛ ~$)

pem : ∀ {A} -> ε ⊢ :- ○ (A ⅋ ¬⁻ A)
pem = case-of (⊢∷ₚₛ ⊎ε
        ((var (𝕫ₛ ⟪ ~$ ,~⟫) · var (𝕫ₛ ⟪~, ~●⁻ ⟫))
            (⊎ε ⊎∷ ⊎⟪ ⊎$L , ⊎●⁻R ⟫))
        ⊢εₚₛ)
    (☺ proof)
    where
        proof : _
        proof ⟪ q , ●⁻ _ ⟫ $̸⟪ r , $̸●⁻ ⟫ = ☹̸𝕫
