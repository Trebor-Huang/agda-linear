-- An abandoned effort
-- This is subsumed by the other modules
-- Therefore I am justified to not leave any more explanation here

module Syntax where

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

data T : Set where
    ▹ : ∀ {p} -> 𝕋 p -> T
    ◃ : ∀ {p} -> 𝕋 p -> T

data J : Set where
    :- : T -> J
    # : J

data Pattern : ∀ p -> 𝕋 p -> Set where
    ⟨_,_⟩ : ∀ {A B} -> Pattern + A -> Pattern + B -> Pattern + (A ⊗ B)
    ϖ₁ : ∀ {A B} -> Pattern + A -> Pattern + (A ⊕ B)
    ϖ₂ : ∀ {A B} -> Pattern + B -> Pattern + (A ⊕ B)
    ⟪_,_⟫ : ∀ {A B} -> Pattern - A -> Pattern - B -> Pattern - (A ⅋ B)
    π₁ : ∀ {A B} -> Pattern - A -> Pattern - (A & B)
    π₂ : ∀ {A B} -> Pattern - B -> Pattern - (A & B)
    *̂ : Pattern + 𝟙
    *̬ : Pattern - ⊥
    ⇑ : ∀ { A : 𝕋 + } -> Pattern - (↑ A)
    ⇓ : ∀ { A : 𝕋 - } -> Pattern + (↓ A)
    ●⁺ : ∀ { A : 𝕋 + } -> Pattern + (¬⁺ A)
    ●⁻ : ∀ { A : 𝕋 - } -> Pattern - (¬⁻ A)

data _∋̂_ : ∀ {p A} -> Pattern p A -> T -> Set where
    ⟨_,~⟩ : ∀ {A B t} {p : Pattern + A} {q : Pattern + B} -> p ∋̂ t -> ⟨ p , q ⟩ ∋̂ t
    ⟨~,_⟩ : ∀ {A B t} {p : Pattern + A} {q : Pattern + B} -> q ∋̂ t -> ⟨ p , q ⟩ ∋̂ t
    ~ϖ₁ : ∀ {A B t} {p : Pattern + A} -> p ∋̂ t -> ϖ₁ {B = B} p ∋̂ t
    ~ϖ₂ : ∀ {A B t} {p : Pattern + B} -> p ∋̂ t -> ϖ₂ {A = A} p ∋̂ t
    ⟪_,~⟫ : ∀ {A B t} {p : Pattern - A} {q : Pattern - B} -> p ∋̂ t -> ⟪ p , q ⟫ ∋̂ t
    ⟪~,_⟫ : ∀ {A B t} {p : Pattern - A} {q : Pattern - B} -> q ∋̂ t -> ⟪ p , q ⟫ ∋̂ t
    ~π₁ : ∀ {A B t} {p : Pattern - A} -> p ∋̂ t -> π₁ {B = B} p ∋̂ t
    ~π₂ : ∀ {A B t} {p : Pattern - B} -> p ∋̂ t -> π₂ {A = A} p ∋̂ t
    ~⇑ : ∀ { A : 𝕋 + } -> ⇑ {A} ∋̂ ▹ A
    ~⇓ : ∀ { A : 𝕋 - } -> ⇓ {A} ∋̂ ◃ A
    ~●⁺ : ∀ {A} -> ●⁺ {A} ∋̂ ◃ A
    ~●⁻ : ∀ {A} -> ●⁻ {A} ∋̂ ▹ A

infix 6 _∋̂_

-- Contexts should respect the structure of bindings
-- Everyone got to be somewhere!

-- Records the Occurence
data Occurs : ∀ {p A} -> Pattern p A -> Set where
    ^⟨_,_⟩ : ∀ {A B} {p : Pattern _ A} {q : Pattern _ B} -> Occurs p -> Occurs q -> Occurs ⟨ p , q ⟩
    ^ϖ₁ : ∀ {A B} {p : Pattern _ A} -> Occurs p -> Occurs (ϖ₁ {B = B} p)
    ^ϖ₂ : ∀ {A B} {p : Pattern _ B} -> Occurs p -> Occurs (ϖ₂ {A = A} p)
    ^⟪_,_⟫ : ∀ {A B} {p : Pattern _ A} {q : Pattern _ B} -> Occurs p -> Occurs q -> Occurs ⟪ p , q ⟫
    ^π₁ : ∀ {A B} {p : Pattern _ A} -> Occurs p -> Occurs (π₁ {B = B} p)
    ^π₂ : ∀ {A B} {p : Pattern _ B} -> Occurs p -> Occurs (π₂ {A = A} p)
    ^*̂ : Occurs *̂
    ^*̬ : Occurs *̬
    □⇑ : ∀ { A : 𝕋 + } -> Occurs (⇑ {A})
    ■⇑ : ∀ { A : 𝕋 + } -> Occurs (⇑ {A})
    □●⁺ : ∀ { A : 𝕋 + } -> Occurs (●⁺ {A})
    ■●⁺ : ∀ { A : 𝕋 + } -> Occurs (●⁺ {A})
    □⇓ : ∀ { A : 𝕋 - } -> Occurs (⇓ {A})
    ■⇓ : ∀ { A : 𝕋 - } -> Occurs (⇓ {A})
    □●⁻ : ∀ { A : 𝕋 - } -> Occurs (●⁻ {A})
    ■●⁻ : ∀ { A : 𝕋 - } -> Occurs (●⁻ {A})

-- Disjoint union of occurrences
data _⊎_≅_ : ∀ {pol A}{p : Pattern pol A} -> Occurs p -> Occurs p -> Occurs p -> Set where
    ⊎⟨_,_⟩ : ∀{A B}{ p : Pattern _ A }{ q : Pattern _ B }{ Δ₁ Δ₂ Δ₃ : Occurs p }{ Γ₁ Γ₂ Γ₃ : Occurs q}
        -> Δ₁ ⊎ Δ₂ ≅ Δ₃ -> Γ₁ ⊎ Γ₂ ≅ Γ₃ -> ^⟨ Δ₁ , Γ₁ ⟩ ⊎ ^⟨ Δ₂ , Γ₂ ⟩ ≅ ^⟨ Δ₃ , Γ₃ ⟩
    ⊎ϖ₁ : ∀{A B}{ p : Pattern + A }{ Δ₁ Δ₂ Δ₃ : Occurs p }
        -> Δ₁ ⊎ Δ₂ ≅ Δ₃ -> ^ϖ₁ Δ₁ ⊎ ^ϖ₁ Δ₂ ≅ ^ϖ₁ {B = B} Δ₃
    ⊎ϖ₂ : ∀{A B}{ p : Pattern + B }{ Δ₁ Δ₂ Δ₃ : Occurs p }
        -> Δ₁ ⊎ Δ₂ ≅ Δ₃ -> ^ϖ₂ Δ₁ ⊎ ^ϖ₂ Δ₂ ≅ ^ϖ₂ {A = A} Δ₃
    ⊎⟪_,_⟫ : ∀{A B}{ p : Pattern _ A }{ q : Pattern _ B }{ Δ₁ Δ₂ Δ₃ : Occurs p }{ Γ₁ Γ₂ Γ₃ : Occurs q}
        -> Δ₁ ⊎ Δ₂ ≅ Δ₃ -> Γ₁ ⊎ Γ₂ ≅ Γ₃ -> ^⟪ Δ₁ , Γ₁ ⟫ ⊎ ^⟪ Δ₂ , Γ₂ ⟫ ≅ ^⟪ Δ₃ , Γ₃ ⟫
    ⊎π₁ : ∀{A B}{ p : Pattern - A }{ Δ₁ Δ₂ Δ₃ : Occurs p }
        -> Δ₁ ⊎ Δ₂ ≅ Δ₃ -> ^π₁ Δ₁ ⊎ ^π₁ Δ₂ ≅ ^π₁ {B = B} Δ₃
    ⊎π₂ : ∀{A B}{ p : Pattern - B }{ Δ₁ Δ₂ Δ₃ : Occurs p }
        -> Δ₁ ⊎ Δ₂ ≅ Δ₃ -> ^π₂ Δ₁ ⊎ ^π₂ Δ₂ ≅ ^π₂ {A = A} Δ₃
    ⊎*̂ : ^*̂ ⊎ ^*̂ ≅ ^*̂
    ⊎*̬ : ^*̬ ⊎ ^*̬ ≅ ^*̬
    ⊎⇑L : ∀{A} -> ■⇑ ⊎ □⇑ ≅ ■⇑ {A}
    ⊎⇑R : ∀{A} -> □⇑ ⊎ ■⇑ ≅ ■⇑ {A}
    ⊎⇑□ : ∀{A} -> □⇑ ⊎ □⇑ ≅ □⇑ {A}
    ⊎⇓L : ∀{A} -> ■⇓ ⊎ □⇓ ≅ ■⇓ {A}
    ⊎⇓R : ∀{A} -> □⇓ ⊎ ■⇓ ≅ ■⇓ {A}
    ⊎⇓□ : ∀{A} -> □⇓ ⊎ □⇓ ≅ □⇓ {A}
    ⊎●⁺L : ∀{A} -> ■●⁺ ⊎ □●⁺ ≅ ■●⁺ {A}
    ⊎●⁺R : ∀{A} -> □●⁺ ⊎ ■●⁺ ≅ ■●⁺ {A}
    ⊎●⁺□ : ∀{A} -> □●⁺ ⊎ □●⁺ ≅ □●⁺ {A}
    ⊎●⁻L : ∀{A} -> ■●⁻ ⊎ □●⁻ ≅ ■●⁻ {A}
    ⊎●⁻R : ∀{A} -> □●⁻ ⊎ ■●⁻ ≅ ■●⁻ {A}
    ⊎●⁻□ : ∀{A} -> □●⁻ ⊎ □●⁻ ≅ □●⁻ {A}

-- Auxiliary functions to construct occurrences
■ : ∀ {pol A} -> (p : Pattern pol A) -> Occurs p
■ ⟨ p , q ⟩ = ^⟨ ■ p , ■ q ⟩
■ (ϖ₁ p) = ^ϖ₁ (■ p)
■ (ϖ₂ p) = ^ϖ₂ (■ p)
■ ⟪ p , q ⟫ = ^⟪ ■ p , ■ q ⟫
■ (π₁ p) = ^π₁ (■ p)
■ (π₂ p) = ^π₂ (■ p)
■ *̂ = ^*̂
■ *̬ = ^*̬
■ ⇑ = ■⇑
■ ⇓ = ■⇓
■ ●⁺ = ■●⁺
■ ●⁻ = ■●⁻

□ : ∀ {pol A} -> (p : Pattern pol A) -> Occurs p
□ ⟨ p , q ⟩ = ^⟨ □ p , □ q ⟩
□ (ϖ₁ p) = ^ϖ₁ (□ p)
□ (ϖ₂ p) = ^ϖ₂ (□ p)
□ ⟪ p , q ⟫ = ^⟪ □ p , □ q ⟫
□ (π₁ p) = ^π₁ (□ p)
□ (π₂ p) = ^π₂ (□ p)
□ *̂ = ^*̂
□ *̬ = ^*̬
□ ⇑ = □⇑
□ ⇓ = □⇓
□ ●⁺ = □●⁺
□ ●⁻ = □●⁻


focus : ∀ {pol A B} -> (p : Pattern pol A) -> p ∋̂ B -> Occurs p
focus ⟨ p , q ⟩ ⟨ α ,~⟩ = ^⟨ focus p α , □ q ⟩
focus ⟨ p , q ⟩ ⟨~, α ⟩ = ^⟨ □ p , focus q α ⟩
focus (ϖ₁ p) (~ϖ₁ α) = ^ϖ₁ (focus p α)
focus (ϖ₂ p) (~ϖ₂ α) = ^ϖ₂ (focus p α)
focus ⟪ p , q ⟫ ⟪ α ,~⟫ = ^⟪ (focus p α) , □ q ⟫
focus ⟪ p , q ⟫ ⟪~, α ⟫ = ^⟪ □ p , (focus q α) ⟫
focus (π₁ p) (~π₁ α) = ^π₁ (focus p α)
focus (π₂ p) (~π₂ α) = ^π₂ (focus p α)
focus ⇑ ~⇑ = ■⇑
focus ⇓ ~⇓ = ■⇓
focus ●⁺ ~●⁺ = ■●⁺
focus ●⁻ ~●⁻ = ■●⁻


-- Now we can properly write some linear code
-- Contexts indicates usage while Stack doesn't

data Stack : Set where
    ∅ : Stack
    _∶_ : ∀ {pol A} -> Stack -> Pattern pol A -> Stack

data Context : Stack -> Set where
    ε : Context ∅
    _∷_ : ∀ {pol A}{p : Pattern pol A}{Σ} -> Context Σ -> Occurs p -> Context (Σ ∶ p)

infix 6 _⊎_≅_
infixl 6 _∷_ _∶_
infix 5 _⊎⊎_≅≅_

-- Extend ⊎ to contexts
data _⊎⊎_≅≅_ : ∀ {Σ} -> Context Σ -> Context Σ -> Context Σ -> Set where
    ⊎⊎ε : ε ⊎⊎ ε ≅≅ ε
    ⊎⊎∷ : ∀ {Σ pol A} {p : Pattern pol A} {Γ₁ Γ₂ Γ₃ : Context Σ} {Δ₁ Δ₂ Δ₃ : Occurs p}
        -> Γ₁ ⊎⊎ Γ₂ ≅≅ Γ₃ -> Δ₁ ⊎ Δ₂ ≅ Δ₃
        -> Γ₁ ∷ Δ₁ ⊎⊎ Γ₂ ∷ Δ₂ ≅≅ Γ₃ ∷ Δ₃

-- Extend □ to contexts
□̂ : ∀ Σ -> Context Σ
□̂ ∅ = ε
□̂ (Σ ∶ α) = (□̂ Σ) ∷ □ α

■̂ : ∀ Σ -> Context Σ
■̂ ∅ = ε
■̂ (Σ ∶ α) = (■̂ Σ) ∷ ■ α

infix 5 _∋_

data _∋_ : ∀ {Σ} -> Context Σ -> T -> Set where
    ŝ_ : ∀ {Σ pol'} {A : T} {B : 𝕋 pol'} {p} {Γ : Context Σ} {Δ}
        -> Γ ∋ A -> (_∷_ {A = B} {p = p} Γ Δ) ∋ A
    ẑ_ : ∀ {Σ pol'} {A : T} {B : 𝕋 pol'} {p}
        -> (α : p ∋̂ A) -> (_∷_ {A = B} {p = p} (□̂ Σ) (focus p α)) ∋ A

infixr 9 ŝ_ ẑ_

-- Sanity Check
𝔹 : 𝕋 +
𝔹 = (𝟙 ⊕ 𝟙)

𝕗 : Pattern + 𝔹
𝕗 = ϖ₁ *̂

𝕥 : Pattern + 𝔹
𝕥 = ϖ₂ *̂

-- For the normal terms!
data _⊨_ : ∀ {Σ} -> Context Σ -> J -> Set
data _⊨⊨_ : ∀ {Σ} -> Context Σ -> ∀ {pol A} (p : Pattern pol A) -> Set

infix 5 _⊨_ _⊨⊨_

data _⊨_ where
    _⟦_⟧⁺ : ∀ {Σ} {Γ : Context Σ} { A : 𝕋 + }
        -> (Δ : Pattern + A)
        -> Γ ⊨⊨ Δ
        -> Γ ⊨ :- (▹ A)
    _⟦_⟧⁻ : ∀ {Σ} {Γ : Context Σ} { A : 𝕋 - }
        -> (Δ : Pattern - A)
        -> Γ ⊨⊨ Δ
        -> Γ ⊨ :- (◃ A)
    case⁺ : ∀ {Σ} {Γ : Context Σ} { A : 𝕋 + }
        -> ((Δ : Pattern + A) -> (Γ ∷ ■ Δ) ⊨ #)
        -> Γ ⊨ :- (◃ A)
    case⁻ : ∀ {Σ} {Γ : Context Σ} { A : 𝕋 - }
        -> ((Δ : Pattern - A) -> (Γ ∷ ■ Δ) ⊨ #)
        -> Γ ⊨ :- (▹ A)
    var : ∀ {Σ} {Γ : Context Σ} { A : T }
        -> Γ ∋ A -> Γ ⊨ :- A
    _#⁺_ : ∀ {Σ} {Γ Γ* Γ' : Context Σ} { A : 𝕋 + }
        -> {σ : Γ ⊎⊎ Γ* ≅≅ Γ'}
        -> (v⁺ : Γ* ∋ ◃ A)
        -> Γ ⊨ :- (▹ A)
        -> Γ' ⊨ #
    _#⁻_ : ∀ {Σ} {Γ Γ* Γ' : Context Σ} { A : 𝕋 - }
        -> {σ : Γ ⊎⊎ Γ* ≅≅ Γ'}
        -> (v⁻ : Γ* ∋ ▹ A)
        -> Γ ⊨ :- (◃ A)
        -> Γ' ⊨ #

infix 6 _#⁺_ _#⁻_
infix 7 _⟦_⟧⁺ _⟦_⟧⁻

data _⊨⊨_ where  -- Just Pattern -> _⊨_
    ⊨⊨*̂ : ∀ {Σ} -> □̂ Σ ⊨⊨ *̂
    ⊨⊨*̬ : ∀ {Σ} -> □̂ Σ ⊨⊨ *̬
    ⊨⊨⇑ : ∀ {Σ A⁺} {Γ : Context Σ}
        -> Γ ⊨ :- (◃ A⁺) -> Γ ⊨⊨ ⇑ {A = A⁺}
    ⊨⊨⇓ : ∀ {Σ A⁻} {Γ : Context Σ}
        -> Γ ⊨ :- (▹ A⁻) -> Γ ⊨⊨ ⇓ {A = A⁻}
    ⊨⊨●⁺ : ∀ {Σ A⁺} {Γ : Context Σ}
        -> Γ ⊨ :- (◃ A⁺) -> Γ ⊨⊨ ●⁺ {A = A⁺}
    ⊨⊨●⁻ : ∀ {Σ A⁻} {Γ : Context Σ}
        -> Γ ⊨ :- (▹ A⁻) -> Γ ⊨⊨ ●⁻ {A = A⁻}
    ⊨⊨⟨_,_⟩ : ∀ {Σ} {Γ₁ Γ₂ Γ₃ : Context Σ} {A⁺ B⁺} {p : Pattern + A⁺} {q : Pattern + B⁺}
        -> {Γ₁ ⊎⊎ Γ₂ ≅≅ Γ₃}
        -> Γ₁ ⊨⊨ p -> Γ₂ ⊨⊨ q -> Γ₃ ⊨⊨ ⟨ p , q ⟩
    ⊨⊨⟪_,_⟫ : ∀ {Σ} {Γ₁ Γ₂ Γ₃ : Context Σ} {A⁻ B⁻} {p : Pattern - A⁻} {q : Pattern - B⁻}
        -> {Γ₁ ⊎⊎ Γ₂ ≅≅ Γ₃}
        -> Γ₁ ⊨⊨ p -> Γ₂ ⊨⊨ q -> Γ₃ ⊨⊨ ⟪ p , q ⟫
    ⊨⊨ϖ₁ : ∀ {Σ} {Γ : Context Σ} {A⁺ B⁺} {p : Pattern + A⁺}
        -> Γ ⊨⊨ p -> Γ ⊨⊨ ϖ₁ {B = B⁺} p
    ⊨⊨ϖ₂ : ∀ {Σ} {Γ : Context Σ} {A⁺ B⁺} {p : Pattern + B⁺}
        -> Γ ⊨⊨ p -> Γ ⊨⊨ ϖ₂ {A = A⁺} p
    ⊨⊨π₁ : ∀ {Σ} {Γ : Context Σ} {A⁻ B⁻} {p : Pattern - A⁻}
        -> Γ ⊨⊨ p -> Γ ⊨⊨ π₁ {B = B⁻} p
    ⊨⊨π₂ : ∀ {Σ} {Γ : Context Σ} {A⁻ B⁻} {p : Pattern - B⁻}
        -> Γ ⊨⊨ p -> Γ ⊨⊨ π₂ {A = A⁻} p

-- Some example terms

tt : ε ⊨ :- (▹ 𝔹)
tt = 𝕥 ⟦ ⊨⊨ϖ₂ ⊨⊨*̂ ⟧⁺

ff : ε ⊨ :- (▹ 𝔹)
ff = 𝕗 ⟦ ⊨⊨ϖ₁ ⊨⊨*̂ ⟧⁺

not : ε ∷ (■ (●⁺ {A = 𝔹})) ⊨ :- (◃ 𝔹)
not = case⁺ n
    where
        n : (b : Pattern + 𝔹) → ε ∷ ■●⁺ ∷ ■ b ⊨ #
        n (ϖ₁ *̂) = _#⁺_
            {σ = ⊎⊎∷ (⊎⊎∷ ⊎⊎ε ⊎●⁺R) (⊎ϖ₁ ⊎*̂)}
            (ŝ ẑ ~●⁺) (𝕥 ⟦ ⊨⊨ϖ₂ ⊨⊨*̂ ⟧⁺)
        n (ϖ₂ *̂) = _#⁺_
            {σ = ⊎⊎∷ (⊎⊎∷ ⊎⊎ε ⊎●⁺R) (⊎ϖ₂ ⊎*̂)}
            (ŝ ẑ ~●⁺) (𝕗 ⟦ ⊨⊨ϖ₁ ⊨⊨*̂ ⟧⁺)
