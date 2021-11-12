module Types where

-- The fundamental types
-- Since this is a non-dependent type theory, this is short and easy

-- Polarity
data ± : Set where
    + : ±
    - : ±

-- The type connectives
data 𝕋 : ± -> Set where
    _⊗_ : 𝕋 + -> 𝕋 + -> 𝕋 +
    _⊕_ : 𝕋 + -> 𝕋 + -> 𝕋 +
    _&_ : 𝕋 - -> 𝕋 - -> 𝕋 -
    _⅋_ : 𝕋 - -> 𝕋 - -> 𝕋 -
    𝟙 : 𝕋 +
    𝟘 : 𝕋 +
    ⊤ : 𝕋 -
    ⊥ : 𝕋 -
    ↑_ : 𝕋 + -> 𝕋 -
    ↓_ : 𝕋 - -> 𝕋 +
    ¬⁺_ : 𝕋 + -> 𝕋 +
    ¬⁻_ : 𝕋 - -> 𝕋 -

infixl 8 _⊗_
infixl 8 _⊕_
infixl 8 _&_
infixl 8 _⅋_

infix 9 ↑_
infix 9 ↓_
infix 9 ¬⁺_
infix 9 ¬⁻_

-- An example type: the booleans
𝟚 : 𝕋 +
𝟚 = 𝟙 ⊕ 𝟙

data Bool : Set where -- I hate standard libraries. I am going to do it myself.
    True : Bool
    False : Bool

-- A "type", as what appears to the left of ⊢
-- It may be a usual type (○ t),
-- Or it may stand for a continuation for t, (● t).
data T : Set where
    ○_ : ∀ {p} -> 𝕋 p -> T
    ●_ : ∀ {p} -> 𝕋 p -> T

-- A judgement, as what appears to the right of ⊢
-- In addition to T, we also have #, standing for a so-called "expression"
-- From a type theoretic point of view, it stands for the result of
-- applying a value to its continuation, which becomes a complete program.
-- From a logical point of view, it means contradiction.
-- However, this is close to the ⊥-contradiction, not 𝟘, so there is no
-- ex falso quodlibet here.
-- The reason that we use # instead of just using ⊥ is that it keeps the syntax
-- symmetric. It also carries connotations about the "focus", which we discuss later.
data J : Set where
    :-_ : T -> J
    # : J

infixr 7 :-_ ○_ ●_
