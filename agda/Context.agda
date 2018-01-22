module Context (Judgement : Set → Set → Set) where

open import Data.List public renaming (_∷_ to _,_)
open import Relation.Nullary
-- open import Relation.Binary.PropositionalEquality

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
    open import Data.Sum

    infix 4 _≈_ _≤_

    _≤_ : Rel (Context V T) _
    R ≤ R' = J ∈ R → J ∈ R'

    -- open import Function.Equivalence

    _≈_ : Rel (Context V T) _
    R ≈ R' = R ≤ R' × R' ≤ R

    ≤-refl : Reflexive _≤_
    ≤-refl = λ x → x

    ≈-refl : Reflexive _≈_
    ≈-refl = ≤-refl -×- ≤-refl

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
    open IsMonoid (Monoid.isMonoid (monoid (Judgement V T))) public

    Context-isMonoid : IsMonoid _≡_ _++_ []
    Context-isMonoid = Monoid.isMonoid (monoid (Judgement V T))

    open import Relation.Binary.PartialOrderReasoning poset public

    propEq : {R S : Context V T} → R ≡ S → R ≈ S
    propEq refl = ≈-refl


    cons-mono : (x : Judgement V T) (R S : Context V T) → R ≤ S → x , R ≤ x , S
    cons-mono _ R S R≤S here = here
    cons-mono x R S R≤S (there p) = there (R≤S p)

    cons-cong : (x : Judgement V T) (R S : Context V T) → R ≈ S → x , R ≈ x , S
    cons-cong x R S (R≤S -×- S≤R) = cons-mono x R S R≤S -×- cons-mono x S R S≤R

    -- beginFrom⟨_⟩_ : ∀ {S R} → J ∈ R → R IsRelatedTo S → J ∈ S
    -- beginFrom⟨_⟩_ {S} {R} J∈R R→S = (begin R→S) J∈R

    --
    --  _++_ related

    insert : (x : Judgement V T) (R S : Context V T) → x ∈ R ++ (x , S)
    insert x [] S = here
    insert x (r , R) S = there (insert x R S)

    prepend : ∀ {R} S → R ≤ S ++ R
    prepend {[]}    S       ()
    prepend {r , R} []      p = p
    prepend {r , R} (s , S) here = insert r (s , S) R
    prepend {r , R} (s , S) (there p) = there (prepend S (there p))

    append : ∀ {R} S → R ≤ R ++ S
    append {[]}    S ()
    append {_ , R} S here        = here
    append {_ , R} S (there J∈R) = there (append S J∈R)

    ++-left-mono : ∀ {R S} T → R ≤ S → T ++ R ≤ T ++ S
    ++-left-mono {R} {S} [] R≤S = R≤S
    ++-left-mono {R} {S} (t , T) R≤S = cons-mono t (T ++ R) (T ++ S) (begin
            T ++ R
        ≤⟨ ++-left-mono {R} {S} T R≤S ⟩
            T ++ S
        ∎)

    ++-left-cong : ∀ {R S} T → R ≈ S → T ++ R ≈ T ++ S
    ++-left-cong {R} {S} T (R≤S -×- S≤R) =
        (++-left-mono {R} {S} T R≤S) -×- (++-left-mono {S} {R} T S≤R)

    shift-left : ∀ (x : Judgement V T) (R : Context V T) → R ++ x , [] ≤ x , R
    shift-left x [] P = P
    shift-left x (_ , R) here = there here
    shift-left x (r , R) (there P) = cons-mono x R (r , R) there (shift-left x R P)

    shift-right : ∀ (x : Judgement V T) (R : Context V T) → x , R ≤ R ++ x , []
    shift-right x [] P = P
    shift-right _ (r , R) here = there (prepend R here)
    shift-right x (r , R) (there P) = cons-mono r R (R ++ x , []) (append (x , [])) P

    swap : (R S : Context V T) → R ++ S ≤ S ++ R
    swap [] S = append []
    swap (r , R) [] = begin
            r , R ++ []
        ≈⟨ propEq (proj₂ identity (r , R)) ⟩
            r , R
        ∎
    swap (r , R) (s , S) = begin
            r , R ++ s , S
        ≤⟨ ++-left-mono (r , R) (shift-right s S) ⟩
            r , R ++ S ++ s , []
        ≈⟨ propEq (sym (assoc (r , R) S (s , []))) ⟩
            r , (R ++ S) ++ s , []
        ≤⟨ shift-left s (r , R ++ S) ⟩
            s , [] ++ r , R ++ S
        ≤⟨ ++-left-mono (s , []) (swap (r , R) S) ⟩
            s , S ++ r , R
        ∎

    ++-right-mono : ∀ {R} {S} (T : Context V T) → R ≤ S → R ++ T ≤ S ++ T
    ++-right-mono {R} {S} T R≤S = begin
            R ++ T
        ≤⟨ swap R T ⟩
            T ++ R
        ≤⟨ ++-left-mono T R≤S ⟩
            T ++ S
        ≤⟨ swap T S ⟩
            S ++ T
        ∎

nub : ∀ {V T : Set} (J K : Judgement V T) (R : Context V T)
    → J ∈ K , R
    → K ∈ R
    → J ∈ R
nub J K  []      J∈         ()
nub J .J (r , R) here       K∈ = K∈
nub J K  (r , R) (there J∈) K∈ = J∈
