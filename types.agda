module Types where

data ± : Set where
    + : ±
    - : ±

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

𝟚 : 𝕋 +
𝟚 = 𝟙 ⊕ 𝟙

data Bool : Set where
    True : Bool
    False : Bool

data T : Set where
    ○_ : ∀ {p} -> 𝕋 p -> T
    ●_ : ∀ {p} -> 𝕋 p -> T

data J : Set where
    :-_ : T -> J
    # : J

infixr 7 :-_ ○_ ●_
