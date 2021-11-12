module Pattern where

open import Types

-- What defines a type is the patterns.
-- Positive types are defined by patterns that constructs its values.
-- Negative types are defined by patterns that specifies its continuation.

-- Patterns do not contain binding-related information.
-- For instance, ⟨ $ , ϖ₁ $ ⟩ is what we usually write as (in Haskell)
-- ( x, Left y ). we use $ as placeholders for pattern variables.
-- This makes a lot of operations on binding structures easier.
-- I will write a separate article on this.

-- A subtlety: The last five patterns are all placeholders for variables.
-- However, apart from $, the other four are 'atomic' variables
-- that we allow. $ signifies 'shallow' pattern matching.

data Pattern : T -> Set where
    ⟨_,_⟩ : ∀ {A⁺ B⁺} -> Pattern (○ A⁺) -> Pattern (○ B⁺) -> Pattern (○ A⁺ ⊗ B⁺)
    ϖ₁ : ∀ {A⁺ B⁺} -> Pattern (○ A⁺) -> Pattern (○ A⁺ ⊕ B⁺)
    ϖ₂ : ∀ {A⁺ B⁺} -> Pattern (○ B⁺) -> Pattern (○ A⁺ ⊕ B⁺)
    ⟪_,_⟫ : ∀ {A⁻ B⁻} -> Pattern (● A⁻) -> Pattern (● B⁻) -> Pattern (● A⁻ ⅋ B⁻)
    π₁ : ∀ {A⁻ B⁻} -> Pattern (● A⁻) -> Pattern (● A⁻ & B⁻)
    π₂ : ∀ {A⁻ B⁻} -> Pattern (● B⁻) -> Pattern (● A⁻ & B⁻)
    *̂ : Pattern (○ 𝟙)
    *̬ : Pattern (● ⊥)
    ⇑ : ∀ A⁺ -> Pattern (○ ↑ A⁺)
    ⇓ : ∀ A⁻ -> Pattern (● ↓ A⁻)
    ●⁺ : ∀ A⁺ -> Pattern (○ ¬⁺ A⁺)
    ●⁻ : ∀ A⁻ -> Pattern (● ¬⁻ A⁻)
    $ : ∀ t -> Pattern t

infix 6 _∋ₚ_
-- We turn to define de Bruijn indices.
-- Note that it is not just unary numbers, but a structured type.
-- This is because the patterns have structures, and we want to respect them.

-- This is just a zipper on Patterns.
data _∋ₚ_ : ∀ {A} -> Pattern A -> T -> Set where
    ⟨_,~⟩ : ∀ {A⁺ B⁺ t} {p : Pattern (○ A⁺)} {q : Pattern (○ B⁺)} -> p ∋ₚ t -> ⟨ p , q ⟩ ∋ₚ t
    ⟨~,_⟩ : ∀ {A⁺ B⁺ t} {p : Pattern (○ A⁺)} {q : Pattern (○ B⁺)} -> q ∋ₚ t -> ⟨ p , q ⟩ ∋ₚ t
    ~ϖ₁ : ∀ {A⁺ B⁺ t} {p : Pattern (○ A⁺)} -> p ∋ₚ t -> ϖ₁ {B⁺ = B⁺} p ∋ₚ t
    ~ϖ₂ : ∀ {A⁺ B⁺ t} {p : Pattern (○ B⁺)} -> p ∋ₚ t -> ϖ₂ {A⁺ = A⁺} p ∋ₚ t
    ⟪_,~⟫ : ∀ {A⁻ B⁻ t} {p : Pattern (● A⁻)} {q : Pattern (● B⁻)} -> p ∋ₚ t -> ⟪ p , q ⟫ ∋ₚ t
    ⟪~,_⟫ : ∀ {A⁻ B⁻ t} {p : Pattern (● A⁻)} {q : Pattern (● B⁻)} -> q ∋ₚ t -> ⟪ p , q ⟫ ∋ₚ t
    ~π₁ : ∀ {A⁻ B⁻ t} {p : Pattern (● A⁻)} -> p ∋ₚ t -> π₁ {B⁻ = B⁻} p ∋ₚ t
    ~π₂ : ∀ {A⁻ B⁻ t} {p : Pattern (● B⁻)} -> p ∋ₚ t -> π₂ {A⁻ = A⁻} p ∋ₚ t
    ~⇑ : ∀ {A⁺} -> ⇑ A⁺ ∋ₚ ● A⁺
    ~⇓ : ∀ {A⁻} -> ⇓ A⁻ ∋ₚ ○ A⁻
    ~●⁺ : ∀ {A⁺} -> ●⁺ A⁺ ∋ₚ ● A⁺
    ~●⁻ : ∀ {A⁻} -> ●⁻ A⁻ ∋ₚ ○ A⁻  -- Subtlety: ○ and ● are not reflected in the syntax for ∋ₚ.
    ~$ : ∀ {t} -> $ t ∋ₚ t

-- We check for pattern coverage, and deepness (i.e. whether the pattern uses $)
infix 9 _≻ₚ_  -- p ≻ₚ q denotes that the pattern p is more general than q.

data _≻ₚ_ : ∀ {A} -> Pattern A -> Pattern A -> Set where
    ≻$ : ∀ {t} (p : Pattern t) -> $ t ≻ₚ p
    -- The rest of these are boilerplate.
    ≻⟨_,_⟩ : ∀ {A⁺ B⁺} {p₁ p₂ : Pattern (○ A⁺)} {q₁ q₂ : Pattern (○ B⁺)}
        -> p₁ ≻ₚ p₂ -> q₁ ≻ₚ q₂ -> ⟨ p₁ , q₁ ⟩ ≻ₚ ⟨ p₂ , q₂ ⟩
    ≻ϖ₁ : ∀ {A⁺ B⁺} {p₁ p₂ : Pattern (○ A⁺)}
        -> p₁ ≻ₚ p₂ -> ϖ₁ {B⁺ = B⁺} p₁ ≻ₚ ϖ₁ {B⁺ = B⁺} p₂
    ≻ϖ₂ : ∀ {A⁺ B⁺} {p₁ p₂ : Pattern (○ B⁺)}
        -> p₁ ≻ₚ p₂ -> ϖ₂ {A⁺ = A⁺} p₁ ≻ₚ ϖ₂ {A⁺ = A⁺} p₂
    ≻⟪_,_⟫ : ∀ {A⁻ B⁻} {p₁ p₂ : Pattern (● A⁻)} {q₁ q₂ : Pattern (● B⁻)}
        -> p₁ ≻ₚ p₂ -> q₁ ≻ₚ q₂ -> ⟪ p₁ , q₁ ⟫ ≻ₚ ⟪ p₂ , q₂ ⟫
    ≻π₁ : ∀ {A⁻ B⁻} {p₁ p₂ : Pattern (● A⁻)}
        -> p₁ ≻ₚ p₂ -> π₁ {B⁻ = B⁻} p₁ ≻ₚ π₁ {B⁻ = B⁻} p₂
    ≻π₂ : ∀ {A⁻ B⁻} {p₁ p₂ : Pattern (● B⁻)}
        -> p₁ ≻ₚ p₂ -> π₂ {A⁻ = A⁻} p₁ ≻ₚ π₂ {A⁻ = A⁻} p₂
    ≻⇑ : ∀ {A⁺} -> ⇑ A⁺ ≻ₚ ⇑ A⁺
    ≻⇓ : ∀ {A⁻} -> ⇓ A⁻ ≻ₚ ⇓ A⁻
    ≻●⁺ : ∀ {A⁺} -> ●⁺ A⁺ ≻ₚ ●⁺ A⁺
    ≻●⁻ : ∀ {A⁻} -> ●⁻ A⁻ ≻ₚ ●⁻ A⁻
    ≻*̂ : *̂ ≻ₚ *̂
    ≻*̬ : *̬ ≻ₚ *̬

data $̸ : ∀ {t} -> Pattern t -> Set where
    -- No clause for $̸$ because it's not deep.
    -- Otherwise we just recurse down the pattern.
    $̸⟨_,_⟩ : ∀ {A⁺ B⁺} {p : Pattern (○ A⁺)} {q : Pattern (○ B⁺)}
        -> $̸ p -> $̸ q -> $̸ ⟨ p , q ⟩
    $̸ϖ₁ : ∀ {A⁺ B⁺} {p : Pattern (○ A⁺)}
        -> $̸ p -> $̸ (ϖ₁ {B⁺ = B⁺} p)
    $̸ϖ₂ : ∀ {A⁺ B⁺} {p : Pattern (○ B⁺)}
        -> $̸ p -> $̸ (ϖ₂ {A⁺ = A⁺} p)
    $̸⟪_,_⟫ : ∀ {A⁻ B⁻} {p : Pattern (● A⁻)} {q : Pattern (● B⁻)}
        -> $̸ p -> $̸ q -> $̸ ⟪ p , q ⟫
    $̸π₁ : ∀ {A⁻ B⁻} {p : Pattern (● A⁻)}
        -> $̸ p -> $̸ (π₁ {B⁻ = B⁻} p)
    $̸π₂ : ∀ {A⁻ B⁻} {p : Pattern (● B⁻)}
        -> $̸ p -> $̸ (π₂ {A⁻ = A⁻} p)
    $̸*̂ : $̸ *̂
    $̸*̬ : $̸ *̬
    $̸⇑ : ∀ {A⁺} -> $̸ (⇑ A⁺)
    $̸⇓ : ∀ {A⁻} -> $̸ (⇓ A⁻)
    $̸●⁺ : ∀ {A⁺} -> $̸ (●⁺ A⁺)
    $̸●⁻ : ∀ {A⁻} -> $̸ (●⁻ A⁻)

-- A list of patterns with the first match semantics.
data Patterns (t : T) : Set where
    εₚ : Patterns t
    _∷ₚ_ : Pattern t -> Patterns t -> Patterns t

infixr 6 _∷ₚ_
infix 5 _∋ₚₛ_

data Maybe (t : Set) : Set where  -- Useful in intermediate computation.
    Just : t -> Maybe t
    Nothing : Maybe t

-- Defined so that we can use idiom brackets in Agda.
pure : ∀ {t} -> t -> Maybe t
pure = Just

_<*>_ : ∀ {t₁ t₂} (f : Maybe (t₁ -> t₂)) -> Maybe t₁ -> Maybe t₂
(Just f) <*> (Just x) = Just (f x)
_ <*> _ = Nothing

-- ps ∋ₚₛ q means that the (deep) pattern q is covered by the list ps.
data _∋ₚₛ_ {t} : Patterns t -> Pattern t -> Set where
    𝕫ₚₛ : ∀ {p ps q} -> $̸ q -> p ≻ₚ q -> p ∷ₚ ps ∋ₚₛ q
    𝕤ₚₛ : ∀ {p ps q} -> ps ∋ₚₛ q -> p ∷ₚ ps ∋ₚₛ q
    -- We allow for failure and eliminate it later.
    ☹ₚₛ : ∀ {ps q} -> $̸ q -> ps ∋ₚₛ q

-- Failure-free version of _∋ₚₛ_.
data ☹̸ {t} : ∀ {ps : Patterns t} {q} -> ps ∋ₚₛ q -> Set where
    ☹̸𝕫 : ∀ {p ps q} {r : $̸ q} {s : p ≻ₚ q} -> ☹̸ (𝕫ₚₛ {p = p} {ps = ps} r s)
    ☹̸𝕤_ : ∀ {p ps q} {r : ps ∋ₚₛ q} -> ☹̸ r -> ☹̸ (𝕤ₚₛ {p = p} r)

infixr 9 ☹̸𝕤_

-- The following functions define the first-match semantics.
cover𝕫 : ∀ t (p : Pattern t) -> (∀ q -> $̸ q -> Maybe (p ≻ₚ q))
cover𝕫 _ ($ t) q r = Just (≻$ q)  -- $ matches everything.
cover𝕫 (○ A ⊗ B) ⟨ p₁ , p₂ ⟩ ⟨ q₁ , q₂ ⟩ $̸⟨ r₁ , r₂ ⟩
    with cover𝕫 (○ A) p₁ q₁ r₁ | cover𝕫 (○ B) p₂ q₂ r₂
... | Just c₁ | Just c₂ = Just ≻⟨ c₁ , c₂ ⟩
... | _       | _       = Nothing
cover𝕫 (○ A ⊕ B) (ϖ₁ p) (ϖ₁ q) ($̸ϖ₁ r)
    with cover𝕫 (○ A) p q r
... | Just c  = Just (≻ϖ₁ c)
... | Nothing = Nothing
cover𝕫 (○ A ⊕ B) (ϖ₁ p) (ϖ₂ q) _ = Nothing
cover𝕫 (○ A ⊕ B) (ϖ₂ p) (ϖ₁ q) _ = Nothing
cover𝕫 (○ A ⊕ B) (ϖ₂ p) (ϖ₂ q) ($̸ϖ₂ r)
    with cover𝕫 (○ B) p q r
... | Just c  = Just (≻ϖ₂ c)
... | Nothing = Nothing
cover𝕫 (● A ⅋ B) ⟪ p₁ , p₂ ⟫ ⟪ q₁ , q₂ ⟫ $̸⟪ r₁ , r₂ ⟫
    with cover𝕫 (● A) p₁ q₁ r₁ | cover𝕫 (● B) p₂ q₂ r₂
... | Just c₁ | Just c₂ = Just ≻⟪ c₁ , c₂ ⟫
... | _       | _       = Nothing
cover𝕫 (● A & B) (π₁ p) (π₁ q) ($̸π₁ r)
    with cover𝕫 (● A) p q r
... | Just c  = Just (≻π₁ c)
... | Nothing = Nothing
cover𝕫 (● A & B) (π₁ p) (π₂ q) _ = Nothing
cover𝕫 (● A & B) (π₂ p) (π₁ q) _ = Nothing
cover𝕫 (● A & B) (π₂ p) (π₂ q) ($̸π₂ r)
    with cover𝕫 (● B) p q r
... | Just c  = Just (≻π₂ c)
... | Nothing = Nothing
cover𝕫 (○ ↑ A⁺) (⇑ A⁺) (⇑ .A⁺) $̸⇑ = Just ≻⇑
cover𝕫 (● ↓ A⁻) (⇓ A⁻) (⇓ .A⁻) $̸⇓ = Just ≻⇓
cover𝕫 (○ ¬⁺ A⁺) (●⁺ A⁺) (●⁺ .A⁺) $̸●⁺ = Just ≻●⁺
cover𝕫 (● ¬⁻ A⁻) (●⁻ A⁻) (●⁻ .A⁻) $̸●⁻ = Just ≻●⁻
cover𝕫 (○ 𝟙) *̂ *̂ $̸*̂ = Just ≻*̂
cover𝕫 (● ⊥) *̬ *̬ $̸*̬ = Just ≻*̬
cover𝕫 _ _ _ r = Nothing

cover𝕤 : ∀ t (ps : Patterns t) (p : Pattern t)
    -> (∀ q -> $̸ q -> ps ∋ₚₛ q) -> (∀ q -> $̸ q -> p ∷ₚ ps ∋ₚₛ q)
cover𝕤 t ps p c q r with cover𝕫 t p q r  -- First match semantics
... | Just c' = 𝕫ₚₛ r c'
... | _       = 𝕤ₚₛ (c q r)

computeCoverage : ∀ {t} (ps : Patterns t) -> (∀ q -> $̸ q -> ps ∋ₚₛ q)
computeCoverage εₚ q = ☹ₚₛ
computeCoverage (x ∷ₚ ps) = cover𝕤 _ ps x (computeCoverage ps)

record Covers (t : T) (ps : Patterns t) : Set where
    constructor ☺
    field
        ☺ : (∀ q r -> ☹̸ (computeCoverage ps q r))

-- Test out the notorious "majority" function pattern
-- The pattern is complete, but you cannot find a natural split variable.
-- The function as written in Agda syntax:
maj : Bool -> Bool -> Bool -> Bool
maj True False x = x
maj False x True = x
maj x True False = x
maj True True True = True
maj False False False = False

-- Some convenient synonyms
pattern ⟨_,_,_⟩ a b c = ⟨ ⟨ a , b ⟩ , c ⟩
pattern $̸⟨_,_,_⟩ a b c = $̸⟨ $̸⟨ a , b ⟩ , c ⟩

pattern 𝕥 = ϖ₂ *̂
pattern 𝕗 = ϖ₁ *̂

pattern $̸𝕥 = $̸ϖ₂ $̸*̂
pattern $̸𝕗 = $̸ϖ₁ $̸*̂

-- The patterns
majₚₛ : Patterns (○ 𝟚 ⊗ 𝟚 ⊗ 𝟚)
majₚₛ = ⟨ 𝕗 , 𝕥 , $ _ ⟩
    ∷ₚ ⟨ 𝕥 , $ _ , 𝕗 ⟩
    ∷ₚ ⟨ $ _ , 𝕗 , 𝕥 ⟩
    ∷ₚ ⟨ 𝕗 , 𝕗 , 𝕗 ⟩
    ∷ₚ ⟨ 𝕥 , 𝕥 , 𝕥 ⟩
    ∷ₚ εₚ

majCovers : Covers (○ 𝟚 ⊗ 𝟚 ⊗ 𝟚) majₚₛ
majCovers = ☺ proof
    where
        proof : _  -- A proof that maj covers every case.
        -- Agda succeeded to infer a lot of things, so
        -- we just have to point out which clause covers which case
        proof _ $̸⟨ $̸𝕗 , $̸𝕗 , $̸𝕗 ⟩ = ☹̸𝕤 ☹̸𝕤 ☹̸𝕤 ☹̸𝕫
        proof _ $̸⟨ $̸𝕥 , $̸𝕗 , $̸𝕗 ⟩ = ☹̸𝕤 ☹̸𝕫
        proof _ $̸⟨ $̸𝕗 , $̸𝕥 , $̸𝕗 ⟩ = ☹̸𝕫
        proof _ $̸⟨ $̸𝕥 , $̸𝕥 , $̸𝕗 ⟩ = ☹̸𝕤 ☹̸𝕫
        proof _ $̸⟨ $̸𝕗 , $̸𝕗 , $̸𝕥 ⟩ = ☹̸𝕤 ☹̸𝕤 ☹̸𝕫
        proof _ $̸⟨ $̸𝕥 , $̸𝕗 , $̸𝕥 ⟩ = ☹̸𝕤 ☹̸𝕤 ☹̸𝕫
        proof _ $̸⟨ $̸𝕗 , $̸𝕥 , $̸𝕥 ⟩ = ☹̸𝕫
        proof _ $̸⟨ $̸𝕥 , $̸𝕥 , $̸𝕥 ⟩ = ☹̸𝕤 ☹̸𝕤 ☹̸𝕤 ☹̸𝕤 ☹̸𝕫

-- Since we are dealing with linear type theory,
-- We need to take care of variable use.
-- Traditionally, the rules are presented with
-- contexts as lists. Then we invent a 'disjoint union' ⊎ concept
-- to state the rules e.g.
-- Γ ⊢ t : A      Γ' ⊢ s : B
-------------------------------
--   Γ ⊎ Γ' ⊢ (t,s) : A × B
-- This requires an awful lot of shifting. We take a much simpler approach:
-- We record all the variables, but mark some of them as used. So Γ and Γ'
-- have the same structure, except that the variable usages are marked differently.
-- ⊎ is then just a straightforward computation.

data Occur : ∀ {t} -> Pattern t -> Set where
    ⟨_,_⟩ₒ : ∀ {A⁺ B⁺} {p : Pattern (○ A⁺)} {q : Pattern (○ B⁺)}
        -> Occur p -> Occur q -> Occur ⟨ p , q ⟩
    ϖ₁ₒ : ∀ {A⁺ B⁺} {p : Pattern (○ A⁺)}
        -> Occur p -> Occur (ϖ₁ {B⁺ = B⁺} p)
    ϖ₂ₒ : ∀ {A⁺ B⁺} {p : Pattern (○ B⁺)} 
        -> Occur p -> Occur (ϖ₂ {A⁺ = A⁺} p)
    ⟪_,_⟫ₒ : ∀ {A⁻ B⁻} {p : Pattern (● A⁻)} {q : Pattern (● B⁻)}
        -> Occur p -> Occur q -> Occur ⟪ p , q ⟫
    π₁ₒ : ∀ {A⁻ B⁻} {p : Pattern (● A⁻)}
        -> Occur p -> Occur (π₁ {B⁻ = B⁻} p)
    π₂ₒ : ∀ {A⁻ B⁻} {p : Pattern (● B⁻)}
        -> Occur p -> Occur (π₂ {A⁻ = A⁻} p)
    *̂ₒ : Occur *̂
    *̬ₒ : Occur *̬
    -- ■ means it is used; □ means it is not used
    -- Basically, treat □ as if it is not there
    -- We keep it only because we want to respect the structure of patterns
    -- Otherwise we might as well just flatten the ■ variables into a list
    ■⇑ₒ : ∀ {A⁺} -> Occur (⇑ A⁺)
    □⇑ₒ : ∀ {A⁺} -> Occur (⇑ A⁺)
    ■⇓ₒ : ∀ {A⁻} -> Occur (⇓ A⁻)
    □⇓ₒ : ∀ {A⁻} -> Occur (⇓ A⁻)
    ■●⁺ₒ : ∀ {A⁺} -> Occur (●⁺ A⁺)
    □●⁺ₒ : ∀ {A⁺} -> Occur (●⁺ A⁺)
    ■●⁻ₒ : ∀ {A⁻} -> Occur (●⁻ A⁻)
    □●⁻ₒ : ∀ {A⁻} -> Occur (●⁻ A⁻)
    ■$ₒ : ∀ {t} -> Occur ($ t)
    □$ₒ : ∀ {t} -> Occur ($ t)

-- Auxiliary functions to construct occurrences
□ : ∀ {t} -> (p : Pattern t) -> Occur p
□ ⟨ p , q ⟩ = ⟨ □ p , □ q ⟩ₒ
□ (ϖ₁ p) = ϖ₁ₒ (□ p)
□ (ϖ₂ p) = ϖ₂ₒ (□ p)
□ ⟪ p , q ⟫ = ⟪ □ p , □ q ⟫ₒ
□ (π₁ p) = π₁ₒ (□ p)
□ (π₂ p) = π₂ₒ (□ p)
□ *̂ = *̂ₒ
□ *̬ = *̬ₒ
□ (⇑ A⁺) = □⇑ₒ
□ (⇓ A⁻) = □⇓ₒ
□ (●⁺ A⁺) = □●⁺ₒ
□ (●⁻ A⁻) = □●⁻ₒ
□ ($ _) = □$ₒ

■ : ∀ {t} -> (p : Pattern t) -> Occur p
■ ⟨ p , q ⟩ = ⟨ ■ p , ■ q ⟩ₒ
■ (ϖ₁ p) = ϖ₁ₒ (■ p)
■ (ϖ₂ p) = ϖ₂ₒ (■ p)
■ ⟪ p , q ⟫ = ⟪ ■ p , ■ q ⟫ₒ
■ (π₁ p) = π₁ₒ (■ p)
■ (π₂ p) = π₂ₒ (■ p)
■ *̂ = *̂ₒ
■ *̬ = *̬ₒ
■ (⇑ A⁺) = ■⇑ₒ
■ (⇓ A⁻) = ■⇓ₒ
■ (●⁺ A⁺) = ■●⁺ₒ
■ (●⁻ A⁻) = ■●⁻ₒ
■ ($ _) = ■$ₒ

-- Marks the one variable in the pattern indicated by (p ∋ₚ t')
■∋ₚ : ∀ {t t'} {p : Pattern t} -> (p ∋ₚ t') -> Occur p
■∋ₚ ⟨ α ,~⟩ = ⟨ ■∋ₚ α , □ _ ⟩ₒ
■∋ₚ ⟨~, α ⟩ = ⟨ □ _ , ■∋ₚ α ⟩ₒ
■∋ₚ (~ϖ₁ α) = ϖ₁ₒ (■∋ₚ α)
■∋ₚ (~ϖ₂ α) = ϖ₂ₒ (■∋ₚ α)
■∋ₚ ⟪ α ,~⟫ = ⟪ ■∋ₚ α , □ _ ⟫ₒ
■∋ₚ ⟪~, α ⟫ = ⟪ □ _ , ■∋ₚ α ⟫ₒ
■∋ₚ (~π₁ α) = π₁ₒ (■∋ₚ α)
■∋ₚ (~π₂ α) = π₂ₒ (■∋ₚ α)
■∋ₚ ~⇑ = ■⇑ₒ
■∋ₚ ~⇓ = ■⇓ₒ
■∋ₚ ~●⁺ = ■●⁺ₒ
■∋ₚ ~●⁻ = ■●⁻ₒ
■∋ₚ ~$ = ■$ₒ

-- A type certificate that two occurrences are disjoint
data _⊎_≅_ : ∀ {t} {p : Pattern t} -> Occur p -> Occur p -> Occur p -> Set where
    ⊎⟨_,_⟩ : ∀ {A B} {p : Pattern (○ A)} {q : Pattern (○ B)}
        -> {Δ₁ Δ₂ Δ₃ : Occur p} {Δ'₁ Δ'₂ Δ'₃ : Occur q}
        -> Δ₁ ⊎ Δ₂ ≅ Δ₃ -> Δ'₁ ⊎ Δ'₂ ≅ Δ'₃ -> ⟨ Δ₁ , Δ'₁ ⟩ₒ ⊎ ⟨ Δ₂ , Δ'₂ ⟩ₒ ≅ ⟨ Δ₃ , Δ'₃ ⟩ₒ
    ⊎ϖ₁ : ∀ {A B} {p : Pattern (○ A)}
        -> {Δ₁ Δ₂ Δ₃ : Occur p}
        -> Δ₁ ⊎ Δ₂ ≅ Δ₃ -> ϖ₁ₒ Δ₁ ⊎ ϖ₁ₒ Δ₂ ≅ ϖ₁ₒ {B⁺ = B} Δ₃
    ⊎ϖ₂ : ∀ {A B} {p : Pattern (○ B)}
        -> {Δ₁ Δ₂ Δ₃ : Occur p}
        -> Δ₁ ⊎ Δ₂ ≅ Δ₃ -> ϖ₂ₒ Δ₁ ⊎ ϖ₂ₒ Δ₂ ≅ ϖ₂ₒ {A⁺ = A} Δ₃
    ⊎⟪_,_⟫ : ∀ {A B} {p : Pattern (● A)} {q : Pattern (● B)}
        -> {Δ₁ Δ₂ Δ₃ : Occur p} {Δ'₁ Δ'₂ Δ'₃ : Occur q}
        -> Δ₁ ⊎ Δ₂ ≅ Δ₃ -> Δ'₁ ⊎ Δ'₂ ≅ Δ'₃ -> ⟪ Δ₁ , Δ'₁ ⟫ₒ ⊎ ⟪ Δ₂ , Δ'₂ ⟫ₒ ≅ ⟪ Δ₃ , Δ'₃ ⟫ₒ
    ⊎π₁ : ∀ {A B} {p : Pattern (● A)}
        -> {Δ₁ Δ₂ Δ₃ : Occur p}
        -> Δ₁ ⊎ Δ₂ ≅ Δ₃ -> π₁ₒ Δ₁ ⊎ π₁ₒ Δ₂ ≅ π₁ₒ {B⁻ = B} Δ₃
    ⊎π₂ : ∀ {A B} {p : Pattern (● B)}
        -> {Δ₁ Δ₂ Δ₃ : Occur p}
        -> Δ₁ ⊎ Δ₂ ≅ Δ₃ -> π₂ₒ Δ₁ ⊎ π₂ₒ Δ₂ ≅ π₂ₒ {A⁻ = A} Δ₃
    ⊎*̂ : *̂ₒ ⊎ *̂ₒ ≅ *̂ₒ
    ⊎*̬ : *̬ₒ ⊎ *̬ₒ ≅ *̬ₒ
    ⊎⇑□ : ∀ {A} -> □⇑ₒ ⊎ □⇑ₒ ≅ □⇑ₒ {A⁺ = A}
    ⊎⇑L : ∀ {A} -> ■⇑ₒ ⊎ □⇑ₒ ≅ ■⇑ₒ {A⁺ = A}
    ⊎⇑R : ∀ {A} -> □⇑ₒ ⊎ ■⇑ₒ ≅ ■⇑ₒ {A⁺ = A}
    ⊎⇓□ : ∀ {A} -> □⇓ₒ ⊎ □⇓ₒ ≅ □⇓ₒ {A⁻ = A}
    ⊎⇓L : ∀ {A} -> ■⇓ₒ ⊎ □⇓ₒ ≅ ■⇓ₒ {A⁻ = A}
    ⊎⇓R : ∀ {A} -> □⇓ₒ ⊎ ■⇓ₒ ≅ ■⇓ₒ {A⁻ = A}
    ⊎●⁺□ : ∀ {A} -> □●⁺ₒ ⊎ □●⁺ₒ ≅ □●⁺ₒ {A⁺ = A}
    ⊎●⁺L : ∀ {A} -> ■●⁺ₒ ⊎ □●⁺ₒ ≅ ■●⁺ₒ {A⁺ = A}
    ⊎●⁺R : ∀ {A} -> □●⁺ₒ ⊎ ■●⁺ₒ ≅ ■●⁺ₒ {A⁺ = A}
    ⊎●⁻□ : ∀ {A} -> □●⁻ₒ ⊎ □●⁻ₒ ≅ □●⁻ₒ {A⁻ = A}
    ⊎●⁻L : ∀ {A} -> ■●⁻ₒ ⊎ □●⁻ₒ ≅ ■●⁻ₒ {A⁻ = A}
    ⊎●⁻R : ∀ {A} -> □●⁻ₒ ⊎ ■●⁻ₒ ≅ ■●⁻ₒ {A⁻ = A}
    ⊎$□ : ∀ {t} -> □$ₒ ⊎ □$ₒ ≅ □$ₒ {t = t}
    ⊎$L : ∀ {t} -> ■$ₒ ⊎ □$ₒ ≅ ■$ₒ {t = t}
    ⊎$R : ∀ {t} -> □$ₒ ⊎ ■$ₒ ≅ ■$ₒ {t = t}

-- Of course, it is decidable.
-- We need dependent pairs, but let's not introduce yet another mixfix.

data Exists (A : Set) (B : A -> Set) : Set where
    exists : ∀ (a : A) (b : B a) -> Exists A B

-- aux functions that have awful type signatures
-- basically just the product morphism:
-- (f × g) (x, y) = (f(x), g(y))
-- But we have dependent types. A mundane dependent type exercise.
pair : ∀ {A B A' B'} -> (f : A -> A') -> (∀ {a} -> B a -> B' (f a))
    -> (Exists A B -> Exists A' B')
pair f g (exists a b) = exists (f a) (g {a} b)

-- A 2-adic version.
pair² : ∀ {A₁ A₂ A B₁ B₂ B} -> (f : A₁ -> A₂ -> A) -> (∀ {a₁ a₂} -> B₁ a₁ -> B₂ a₂ -> B (f a₁ a₂))
    -> (Exists A₁ B₁ -> Exists A₂ B₂ -> Exists A B)
pair² f g (exists a₁ b₁) (exists a₂ b₂) = exists (f a₁ a₂) (g b₁ b₂)

-- We implement the decision procedure.
-- It doesn't explain why it fails, but always carries a proof when it succeeds.
_⊎_ : ∀ {t} {p : Pattern t} -> (Δ₁ Δ₂ : Occur p) -> Maybe (Exists _ \Δ -> Δ₁ ⊎ Δ₂ ≅ Δ)
⟨ Δ₁ , Δ₃ ⟩ₒ ⊎ ⟨ Δ₂ , Δ₄ ⟩ₒ = ⦇ (pair² ⟨_,_⟩ₒ ⊎⟨_,_⟩) (Δ₁ ⊎ Δ₂) (Δ₃ ⊎ Δ₄) ⦈
ϖ₁ₒ Δ₁ ⊎ ϖ₁ₒ Δ₂ = ⦇ (pair ϖ₁ₒ ⊎ϖ₁) (Δ₁ ⊎ Δ₂) ⦈
ϖ₂ₒ Δ₁ ⊎ ϖ₂ₒ Δ₂ = ⦇ (pair ϖ₂ₒ ⊎ϖ₂) (Δ₁ ⊎ Δ₂) ⦈
⟪ Δ₁ , Δ₃ ⟫ₒ ⊎ ⟪ Δ₂ , Δ₄ ⟫ₒ = ⦇ (pair² ⟪_,_⟫ₒ ⊎⟪_,_⟫) (Δ₁ ⊎ Δ₂) (Δ₃ ⊎ Δ₄) ⦈
π₁ₒ Δ₁ ⊎ π₁ₒ Δ₂ = ⦇ (pair π₁ₒ ⊎π₁) (Δ₁ ⊎ Δ₂) ⦈
π₂ₒ Δ₁ ⊎ π₂ₒ Δ₂ = ⦇ (pair π₂ₒ ⊎π₂) (Δ₁ ⊎ Δ₂) ⦈
*̂ₒ ⊎ *̂ₒ = Just (exists *̂ₒ ⊎*̂)
*̬ₒ ⊎ *̬ₒ = Just (exists *̬ₒ ⊎*̬)
■⇑ₒ ⊎ ■⇑ₒ = Nothing
■⇑ₒ ⊎ □⇑ₒ = Just (exists ■⇑ₒ ⊎⇑L)
□⇑ₒ ⊎ ■⇑ₒ = Just (exists ■⇑ₒ ⊎⇑R)
□⇑ₒ ⊎ □⇑ₒ = Just (exists □⇑ₒ ⊎⇑□)
■⇓ₒ ⊎ ■⇓ₒ = Nothing
■⇓ₒ ⊎ □⇓ₒ = Just (exists ■⇓ₒ ⊎⇓L)
□⇓ₒ ⊎ ■⇓ₒ = Just (exists ■⇓ₒ ⊎⇓R)
□⇓ₒ ⊎ □⇓ₒ = Just (exists □⇓ₒ ⊎⇓□)
■●⁺ₒ ⊎ ■●⁺ₒ = Nothing
■●⁺ₒ ⊎ □●⁺ₒ = Just (exists ■●⁺ₒ ⊎●⁺L)
□●⁺ₒ ⊎ ■●⁺ₒ = Just (exists ■●⁺ₒ ⊎●⁺R)
□●⁺ₒ ⊎ □●⁺ₒ = Just (exists □●⁺ₒ ⊎●⁺□)
■●⁻ₒ ⊎ ■●⁻ₒ = Nothing
■●⁻ₒ ⊎ □●⁻ₒ = Just (exists ■●⁻ₒ ⊎●⁻L)
□●⁻ₒ ⊎ ■●⁻ₒ = Just (exists ■●⁻ₒ ⊎●⁻R)
□●⁻ₒ ⊎ □●⁻ₒ = Just (exists □●⁻ₒ ⊎●⁻□)
■$ₒ ⊎ ■$ₒ = Nothing
■$ₒ ⊎ □$ₒ = Just (exists ■$ₒ ⊎$L)
□$ₒ ⊎ ■$ₒ = Just (exists ■$ₒ ⊎$R)
□$ₒ ⊎ □$ₒ = Just (exists □$ₒ ⊎$□)

infixr 6 _⊎_
