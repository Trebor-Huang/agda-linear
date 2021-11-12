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

■̂ : ∀ {Σ} -> StrictContext Σ

□̂ : ∀ {Σ} -> StrictContext Σ

infix 6 _∋̂_
data _∋̂_ : StrictStack -> T -> Set where 

■̂∋ : ∀ {Σ t} -> Σ ∋̂ t -> StrictContext Σ
-- TODO

data _⊎̂_≅̂_ : ∀ {Σ} -> StrictContext Σ -> StrictContext Σ -> StrictContext Σ -> Set where
-- TODO

data _⊨_ : ∀ {Σ} -> StrictContext Σ -> J -> Set
data _⊨̅_ : ∀ {Σ} -> StrictContext Σ -> StrictStack -> Set
data _⊨ₚ_ : ∀ {Σ t} {p : Pattern t} -> StrictContext Σ -> $̸ p -> Set
data _ʻ_⊨ₚₛ# : ∀ {Σ t} {ps : Patterns t} -> StrictContext Σ -> $̸ₚₛ ps -> Set

data _⊨_ where
    _⟦_⟧⁺ : ∀ {Σ} {Γ : StrictContext Σ} { A : 𝕋 + } {p : Pattern (○ A)}
        -> (p̃ : $̸ p) -> Γ ⊨ₚ p̃ -> Γ ⊨ :- ○ A
    _⟦_⟧⁻ : ∀ {Σ} {Γ : StrictContext Σ} { A : 𝕋 - } {p : Pattern (● A)}
        -> (p̃ : $̸ p) -> Γ ⊨ₚ p̃ -> Γ ⊨ :- ● A
    case⁺ : ∀ {Σ} {Γ : StrictContext Σ} { A : 𝕋 + } {ps : Patterns (○ A)}
        -> (p̃s : $̸ₚₛ ps) -> Γ ʻ p̃s ⊨ₚₛ# -> Covers (○ A) ps -> Γ ⊨ :- ● A
    case⁻ : ∀ {Σ} {Γ : StrictContext Σ} { A : 𝕋 - } {ps : Patterns (● A)}
        -> (p̃s : $̸ₚₛ ps) -> Γ ʻ p̃s ⊨ₚₛ# -> Covers (● A) ps -> Γ ⊨ :- ○ A
    _·⁺_ : ∀ {Σ} {Γ Γ' : StrictContext Σ} { A : 𝕋 + }
        -> Γ ⊨ :- ○ A -> (v : Σ ∋̂ ● A)
        -> {Γ ⊎̂ (■̂∋ v) ≅̂ Γ'} -> Γ' ⊨ #
    _·⁻_ : ∀ {Σ} {Γ Γ' : StrictContext Σ} { A : 𝕋 - }
        -> Γ ⊨ :- ● A -> (v : Σ ∋̂ ○ A)
        -> {Γ ⊎̂ (■̂∋ v) ≅̂ Γ'} -> Γ' ⊨ #

data _⊨̅_ where

data _⊨ₚ_ where

data _ʻ_⊨ₚₛ# where
