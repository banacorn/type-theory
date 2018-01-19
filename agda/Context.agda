module Context (Judgement : Set → Set → Set) where

open import Data.List public renaming (_∷_ to _,_)

Context : Set → Set → Set
Context V T = List (Judgement V T)

infix 4 _∈_

data _∈_ {V T} : Judgement V T → Context V T → Set where
    here  : ∀ {  x A}         → x ∈ x , A
    there : ∀ {a x A} → x ∈ A → x ∈ a , A

module Inc {V T : Set} (J : Judgement V T) where

    open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to _-×-_)
    open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)
    open import Relation.Binary
    open import Relation.Unary hiding (_∈_)

    infix 4 _≈_ _≤_

    _≤_ : Rel (Context V T) _
    R ≤ R' = J ∈ R → J ∈ R'

    -- open import Function.Equivalence

    _≈_ : Rel (Context V T) _
    R ≈ R' = R ≤ R' × R' ≤ R

    ≈-refl : ∀ {R} → R ≈ R
    ≈-refl = (λ x → x) -×- (λ x → x)

    ≈-isEquivalence : IsEquivalence _≈_
    ≈-isEquivalence = record
        { refl = ≈-refl
        ; sym = λ x → (proj₂ x) -×- (proj₁ x)
        ; trans = λ f≈g g≈h → (λ z → proj₁ g≈h (proj₁ f≈g z)) -×- (λ z → proj₂ f≈g (proj₂ g≈h z))
        }

    preorder : IsPreorder _≈_ _≤_
    preorder = record
        { isEquivalence = ≈-isEquivalence
        ; reflexive = λ A≈B J∈A → proj₁ A≈B J∈A
        ; trans = λ A≤B B≤C J∈A → B≤C (A≤B J∈A)
        }

    partialOrder : IsPartialOrder _≈_ _≤_
    partialOrder = record
        { isPreorder = preorder
        ; antisym = λ A≤B B≤A → A≤B -×- B≤A
        }

    poset : Poset _ _ _
    poset = record
        { Carrier = Context V T
        ; _≈_ = _≈_
        ; _≤_ = _≤_
        ; isPartialOrder = partialOrder
        }

    open import Algebra using (Monoid)
    open import Algebra.Structures using (IsMonoid)
    open IsMonoid (Monoid.isMonoid (monoid (Judgement V T)))

    Context-isMonoid : IsMonoid _≡_ _++_ []
    Context-isMonoid = Monoid.isMonoid (monoid (Judgement V T))

    open import Relation.Binary.PartialOrderReasoning poset

    -- beginFrom⟨_⟩_ : ∀ {S R} → J ∈ R → R IsRelatedTo S → J ∈ S
    -- beginFrom⟨_⟩_ {S} {R} J∈R R→S = (begin R→S) J∈R

    cons-cong : (x : Judgement V T) (R S : Context V T) → R ≈ S → x , R ≈ x , S
    cons-cong x R S (R≤S -×- S≤R) = lemma R≤S -×- lemma S≤R
        where
            lemma : ∀ {P Q} → P ≤ Q → x , P ≤ x , Q
            lemma P≤Q here = here
            lemma P≤Q (there p) = there (P≤Q p)

    propEq : {R S : Context V T} → R ≡ S → R ≈ S
    propEq refl = ≈-refl

    --
    --  _++_ related

    insert : (x : Judgement V T) (R S : Context V T) → x ∈ R ++ (x , S)
    insert x [] S = here
    insert x (r , R) S = there (insert x R S)

    prepend : (R S : Context V T) → R ≤ S ++ R
    prepend []      S       ()
    prepend (r , R) []      p = p
    prepend (r , R) (s , S) here = {!   !}
     -- insert r (s , S) R
    prepend (r , R) (s , S) (there p) = there (prepend (r , R) S (there p))

    append : (R S : Context V T) → R ≤ R ++ S
    append []      S ()
    append (_ , R) S here        = here
    append (_ , R) S (there J∈R) = there (append R S J∈R)

    ++-cong : (R S T : Context V T) → R ≈ S → T ++ R ≈ T ++ S
    ++-cong [] [] T R≈S = ≈-refl
    ++-cong [] (s , S) [] R≈S = R≈S
    ++-cong [] (s , S) (t , T) (proj₃ -×- proj₄) = {!   !}
    ++-cong (r , R) S T R≈S = {!   !}


    -- ++-either : (j : Judgement V T) (R S : Context V T)
    --     → R ++ S ≤ R ∪ S
    -- ++-either = {!   !}

    swap : (R S : Context V T) → R ++ S ≈ S ++ R
    swap [] []      = ≈-refl
    swap [] (x , S) = cons-cong x S (S ++ []) (propEq (PropEq.sym (proj₂ identity S)))
    swap (x , R) [] = cons-cong x (R ++ []) R (propEq (proj₂ identity R))
    swap (r , R) (s , S) = to -×- {!   !}
        where
            to : r , R ++ s , S ≤ s , S ++ r , R
            to here = (begin
                    J , []
                ≤⟨ append (J , []) R ⟩
                    J , R
                ≤⟨ prepend (J , R) (s , S) ⟩
                    s , S ++ J , R
                ∎) here
            to (there p) = (begin
                    R ++ s , S
                ≤⟨ {!  !} ⟩
                    {!   !}
                ≤⟨ {!  !} ⟩
                    {!   !}
                ≈⟨ {!  swap !} ⟩
                    {!   !}
                ≈⟨ {!  swap  !} ⟩
                -- ≈⟨ swap R (s , S) ⟩
                --     s , S ++ R
                -- ≈⟨ {!  swap !} ⟩
                    -- {!   !}
                -- ≤⟨ prepend (R ++ s , S) (r , []) ⟩
                --     r , R ++ s , S
                -- ≈⟨ swap (r , R) (s , S) ⟩
                -- ≈⟨ {!  swap !} ⟩
                    -- {!   !}
                    s , S ++ r , R
                ∎) p
        --     lemma : ∀ {P Q} → P ≤ Q → J ∈ x , P → J ∈ x , Q
        --     lemma P≤Q here = here
        --     lemma P≤Q (there p) = there (P≤Q p)

            -- open import Algebra.Structures
        -- where
        --     open
    -- prepend : (R S : Context V T) → R ≤ S ++ R
    -- prepend []      S ()
    -- prepend (_ , R) S here        = here
    -- prepend (x , R) S (there J∈R) = there (append R S J∈R)



-- Inc : ∀ {V T} (J : Judgement V T) → Rel (Context V T) _
-- Inc J R R' = J ∈ R → J ∈ R'
--
-- ∈-++ : ∀ {V T} (J : Judgement V T) (R R' : Context V T) → Inc J R (R ++ R')
-- ∈-++ J []        R' ()
-- ∈-++ J (.J , xs) R' here        = here
-- ∈-++ J (x  , xs) R' (there J∈R) = there (∈-++ J xs R' J∈R)
--
-- ∈-≡ : ∀ {V T} {J : Judgement V T} {R R' : Context V T} → R ≡ R' → Inc J R R'
-- ∈-≡ {V} {T} {J} {R} {.R} refl = λ x → x
--
-- isPreorder : {!   !}
-- isPreorder = {!   !}
