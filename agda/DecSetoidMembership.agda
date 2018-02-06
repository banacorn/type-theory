open import Relation.Binary

module DecSetoidMembership {c ℓ} (A : DecSetoid c ℓ) where

open import Data.List
open import Data.Product using (_×_; _,_; proj₁; proj₂)
-- open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Level

open DecSetoid A hiding (preorder)

≈-refl : Reflexive _≈_
≈-refl = IsEquivalence.refl isEquivalence

-- Membership
infix 3 _∈_ _∈?_
data _∈_ : Carrier → (List Carrier) → Set (c ⊔ ℓ) where
    here  : {x y : Carrier} {xs : List Carrier} → x ≈ y → x ∈ y ∷ xs
    there : {x y : Carrier} {xs : List Carrier} → x ∈ xs → x ∈ y ∷ xs

transport : ∀ {x' x xs} → x' ≈ x → x ∈ xs → x' ∈ xs
transport x'≈x (here p) = here (trans x'≈x p)
transport x'≈x (there p) = there (transport x'≈x p)

∈?-lemma : ∀ {x x' xs} → ¬ (x ≈ x') → ¬ (x ∈ xs) → ¬ (x ∈ x' ∷ xs)
∈?-lemma x≉x' x∉xs (here x≈x') = contradiction x≈x' x≉x'
∈?-lemma x≉x' x∉xs (there x∈xs) = contradiction x∈xs x∉xs

_∈?_ : (x : Carrier) → (xs : List Carrier) → Dec (x ∈ xs)
x ∈? []        = no (λ ())
x ∈? (x' ∷ xs) with x ≟ x'
x ∈? (x' ∷ xs) | yes p = yes (here p)
x ∈? (x' ∷ xs) | no ¬p with x ∈? xs
x ∈? (x' ∷ xs) | no ¬p | yes q = yes (there q)
x ∈? (x' ∷ xs) | no ¬p | no ¬q = no (∈?-lemma ¬p ¬q)

-- Subset
infix 4 _⊆_
infix 3 _≋_
_⊆_ : Rel (List Carrier) _
P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q

-- Two sets are considered equal when they subsume one another
_≋_ : Rel (List Carrier) _
R ≋ R' = R ⊆ R' × R' ⊆ R

⊆-refl : Reflexive _⊆_
⊆-refl x = x

≋-refl : Reflexive _≋_
≋-refl = ⊆-refl , ⊆-refl

≋-sym : Symmetric _≋_
≋-sym x = (proj₂ x) , (proj₁ x)

≋-trans : Transitive _≋_
≋-trans f≋g g≋h = (λ z → proj₁ g≋h (proj₁ f≋g z)) , (λ z → proj₂ f≋g (proj₂ g≋h z))

≋-isEquivalence : IsEquivalence _≋_
≋-isEquivalence = record
    { refl = ≋-refl
    ; sym = ≋-sym
    ; trans = ≋-trans
    }

⊆-trans : Transitive _⊆_
⊆-trans = λ A≤B B≤C J∈A → B≤C (A≤B J∈A)

preorder : IsPreorder _≋_ _⊆_
preorder = record
    { isEquivalence = ≋-isEquivalence
    ; reflexive = λ A≋B J∈A → proj₁ A≋B J∈A
    ; trans = ⊆-trans
    }

partialOrder : IsPartialOrder _≋_ _⊆_
partialOrder = record
    { isPreorder = preorder
    ; antisym = λ A≤B B≤A → A≤B , B≤A
    }

poset : Poset _ _ _
poset = record
    { Carrier = List Carrier
    ; _≈_ = _≋_
    ; _≤_ = _⊆_
    ; isPartialOrder = partialOrder
    }

open import Algebra using (Monoid)
open import Algebra.Structures using (IsMonoid)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
open IsMonoid (Monoid.isMonoid (monoid Carrier)) public

Context-isMonoid : IsMonoid _≡_ _++_ []
Context-isMonoid = Monoid.isMonoid (monoid Carrier)

open import Relation.Binary.PartialOrderReasoning poset public

propEq : {R S : List Carrier} → R ≡ S → R ≋ S
propEq PropEq.refl = ≋-refl

∷-mono : (x : Carrier) {R S : List Carrier} → R ⊆ S → x ∷ R ⊆ x ∷ S
∷-mono _ R≤S (here p) = here p
∷-mono x R≤S (there p) = there (R≤S p)

∷-cong : (x : Carrier) (R S : List Carrier) → R ≋ S → x ∷ R ≋ x ∷ S
∷-cong x R S (R≤S , S≤R) = (∷-mono x R≤S) , (∷-mono x S≤R)

insert : (x : Carrier) (R S : List Carrier) → x ∈ R ++ (x ∷ S)
insert x []      S = here ≈-refl
insert x (r ∷ R) S = there (insert x R S)

prepend : ∀ {R} S → R ⊆ S ++ R
prepend {[]}    S       ()
prepend {r ∷ R} []      p = p
prepend {r ∷ R} (s ∷ S) (here p) = transport p (insert r (s ∷ S) R) -- insert r (s ∷ S) R
prepend {r ∷ R} (s ∷ S) (there p) = there (prepend S (there p))

append : ∀ {R} S → R ⊆ R ++ S
append {[]}    S ()
append {_ ∷ R} S (here p)    = here p
append {_ ∷ R} S (there p) = there (append S p)

++-left-mono : ∀ {R S} T → R ⊆ S → T ++ R ⊆ T ++ S
++-left-mono {R} {S} [] R≤S = R≤S
++-left-mono {R} {S} (t ∷ T) R≤S = ∷-mono t (begin
        T ++ R
    ≤⟨ ++-left-mono {R} {S} T R≤S ⟩
        T ++ S
    ∎)

++-left-cong : ∀ {R S} T → R ≋ S → T ++ R ≋ T ++ S
++-left-cong {R} {S} T (R≤S , S≤R) =
    (++-left-mono {R} {S} T R≤S) , (++-left-mono {S} {R} T S≤R)

shift-left : ∀ (x : Carrier) (R : List Carrier) → R ++ x ∷ [] ⊆ x ∷ R
shift-left x [] P = P
shift-left x (_ ∷ R) (here p) = there (here p)
shift-left x (r ∷ R) (there p) = ∷-mono x there (shift-left x R p)

shift-right : ∀ (x : Carrier) (R : List Carrier) → x ∷ R ⊆ R ++ x ∷ []
shift-right x [] P = P
shift-right _ (r ∷ R) (here p) = transport p (there (prepend R (here ≈-refl)))
shift-right x (r ∷ R) (there p) = ∷-mono r (append (x ∷ [])) p

-- swap : (R S : List Carrier) → R ++ S ⊆ S ++ R
-- swap []      S  = append []
-- swap (r ∷ R) [] = begin
--         r ∷ R ++ []
--     ≋⟨ propEq (proj₂ identity (r ∷ R)) ⟩
--         r ∷ R
--     ∎
-- swap (r ∷ R) (s ∷ S) = begin
--         r ∷ R ++ s ∷ S
--     ≤⟨ ++-left-mono (r ∷ R) (shift-right s S) ⟩
--         r ∷ R ++ S ++ s ∷ []
--     ≋⟨ propEq (sym (assoc (r ∷ R) S (s ∷ []))) ⟩
--         r ∷ (R ++ S) ++ s ∷ []
--     ≤⟨ shift-left s (r ∷ R ++ S) ⟩
--         s ∷ [] ++ r ∷ R ++ S
--     ≤⟨ ++-left-mono (s ∷ []) (swap (r ∷ R) S) ⟩
--         s ∷ S ++ r ∷ R
--     ∎
--
-- ++-right-mono : ∀ {R} {S} (T : List Carrier) → R ⊆ S → R ++ T ⊆ S ++ T
-- ++-right-mono {R} {S} T R≤S = begin
--         R ++ T
--     ≤⟨ swap R T ⟩
--         T ++ R
--     ≤⟨ ++-left-mono T R≤S ⟩
--         T ++ S
--     ≤⟨ swap T S ⟩
--         S ++ T
--     ∎

nub : ∀ {xs y} → y ∈ xs → y ∷ xs ⊆ xs
nub {[]}     ()   x∈y∷xs
nub {x ∷ xs} y∈xs (here p)  = transport p y∈xs
nub {x ∷ xs} y∈xs (there p) = p

-- ∈-refl : ∀ {x : A} {xs : List Carrier} → x ∈ x ∷ xs
-- ∈-refl = here
--
-- ∈-weakening : ∀ {y : A} {xs : List Carrier} → xs ⊆ y ∷ xs
-- ∈-weakening = there
--
-- ∈-++-weakening : ∀ {xs ys : List Carrier} → xs ⊆ xs ++ ys
-- ∈-++-weakening here      = here
-- ∈-++-weakening (there p) = there (∈-++-weakening p)
--
-- ∈-trans : ∀ {y : A} {xs : List Carrier} → y ∈ xs → y ∷ xs ⊆ xs
-- ∈-trans y∈xs here      = y∈xs
-- ∈-trans y∈xs (there p) = p
