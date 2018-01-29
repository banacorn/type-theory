module NaturalDeduction (Judgement : Set) where

open import Data.List public renaming (_∷_ to _,_)

Context : Set
Context = List Judgement

infix 3 _⊢_

-- There can only be one "succedent" in Natural Deduction
data _⊢_ : Context → Judgement → Set where
    here  : ∀ {  x A}         → x , A ⊢ x
    there : ∀ {a x A} → A ⊢ x → a , A ⊢ x

module Fixed (J : Judgement) where

    open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to _-×-_)
    open import Relation.Binary.PropositionalEquality as ≡⇒≈ using (_≡_; refl)
    open import Relation.Binary

    infix 4 _≈_ _≤_

    _≤_ : Rel Context _
    R ≤ S = R ⊢ J → S ⊢ J

    _≈_ : Rel Context _
    R ≈ S = R ≤ S × S ≤ R

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
        { Carrier = Context
        ; _≈_ = _≈_
        ; _≤_ = _≤_
        ; isPartialOrder = partialOrder
        }

    open import Algebra using (Monoid)
    open import Algebra.Structures using (IsMonoid)
    open IsMonoid (Monoid.isMonoid (monoid Judgement)) public

    Context-isMonoid : IsMonoid _≡_ _++_ []
    Context-isMonoid = Monoid.isMonoid (monoid Judgement)

    open import Relation.Binary.PartialOrderReasoning poset public

    ++-right-identity : ∀ xs → xs ++ [] ≡ xs
    ++-right-identity = proj₂ identity

    ≡⇒≈ : {R S : Context} → R ≡ S → R ≈ S
    ≡⇒≈ refl = ≈-refl

    infixr 2 _≡⟨_⟩_
    _≡⟨_⟩_ : ∀ x {y z} → x ≡ y → y IsRelatedTo z → x IsRelatedTo z
    _ ≡⟨ x≡y ⟩ y~z = _ ≈⟨ ≡⇒≈ x≡y ⟩ y~z

    cons-mono : (x : Judgement) (R S : Context) → R ≤ S → x , R ≤ x , S
    cons-mono _ R S R≤S here = here
    cons-mono x R S R≤S (there p) = there (R≤S p)

    cons-cong : (x : Judgement) (R S : Context) → R ≈ S → x , R ≈ x , S
    cons-cong x R S (R≤S -×- S≤R) = cons-mono x R S R≤S -×- cons-mono x S R S≤R

    insert : (x : Judgement) (R S : Context) → R ++ (x , S) ⊢ x
    insert x []      S = here
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

    shift-left : ∀ (x : Judgement) (R : Context) → R ++ x , [] ≤ x , R
    shift-left x [] P = P
    shift-left x (_ , R) here = there here
    shift-left x (r , R) (there P) = cons-mono x R (r , R) there (shift-left x R P)

    shift-right : ∀ (x : Judgement) (R : Context) → x , R ≤ R ++ x , []
    shift-right x [] P = P
    shift-right _ (r , R) here = there (prepend R here)
    shift-right x (r , R) (there P) = cons-mono r R (R ++ x , []) (append (x , [])) P

    swap : (R S : Context) → R ++ S ≤ S ++ R
    swap [] S = append []
    swap (r , R) [] = begin
            r , R ++ []
        ≡⟨ ++-right-identity (r , R) ⟩
            r , R
        ∎
    swap (r , R) (s , S) = begin
            r , R ++ s , S
        ≤⟨ ++-left-mono (r , R) (shift-right s S) ⟩
            r , R ++ S ++ s , []
        ≡⟨ sym (assoc (r , R) S (s , [])) ⟩
            r , (R ++ S) ++ s , []
        ≤⟨ shift-left s (r , R ++ S) ⟩
            s , [] ++ r , R ++ S
        ≤⟨ ++-left-mono (s , []) (swap (r , R) S) ⟩
            s , S ++ r , R
        ∎

    ++-right-mono : ∀ {R} {S} (T : Context) → R ≤ S → R ++ T ≤ S ++ T
    ++-right-mono {R} {S} T R≤S = begin
            R ++ T
        ≤⟨ swap R T ⟩
            T ++ R
        ≤⟨ ++-left-mono T R≤S ⟩
            T ++ S
        ≤⟨ swap T S ⟩
            S ++ T
        ∎

-- Reflexivity: Every judgment is a consequence of itself: J , Γ ⊢ J.
--              Each hypothesis justifies itself as conclusion.
⊢-refl : ∀ Γ J → J , Γ ⊢ J
⊢-refl Γ J = here

-- Weakening:   If Γ ⊢ J, then K, Γ ⊢ J.
--              Entailment is not influenced by un-exercised options.
⊢-weakening : ∀ Γ J K → Γ ⊢ J → K , Γ ⊢ J
⊢-weakening Γ J K Γ⊢J = there Γ⊢J

-- Transitivity: If Γ, K ⊢ J and Γ ⊢ K, then Γ ⊢ J. If we replace an axiom by a
--               derivation of it, the result is a derivation of its consequent
--               without that hypothesis.
⊢-trans : ∀ Γ J K → K , Γ ⊢ J → Γ ⊢ K → Γ ⊢ J
⊢-trans Γ J .J here          Γ⊢K = Γ⊢K
⊢-trans Γ J K  (there K,Γ⊢J) Γ⊢K = K,Γ⊢J

-- record Conjunction (A B : Judgement) : Judgement

-- ∧-I : ∀ A B → (_∧_ : Judgement → Judgement → Judgement) → ∀ Γ Δ → Γ ⊢ A → Γ ⊢ A →

-- data NJ : Set where
