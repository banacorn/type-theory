open import Data.List using (List)

module Entailment (Judgement : Set) where

open import Data.List public renaming (_∷_ to _,_)
open import Level

Context : Set
Context = List Judgement

Rule : Set₁
Rule = Context → Judgement → Set

-- Membership
infix 3 _∈_
data _∈_ {ℓ} {A : Set ℓ} : A → (List A) → Set ℓ where
    here  : {x   : A} {xs : List A}          → x ∈ x , xs
    there : {x y : A} {xs : List A} → x ∈ xs → x ∈ y , xs

∈-refl : ∀ {ℓ} {A : Set ℓ} {x : A} {xs : List A} → x ∈ x , xs
∈-refl = here

∈-weakening : ∀ {ℓ} {A : Set ℓ} {x y : A} {xs : List A} → x ∈ xs → x ∈ y , xs
∈-weakening = there

∈-++-weakening : ∀ {ℓ} {A : Set ℓ} {x : A} {xs ys : List A} → x ∈ xs → x ∈ xs ++ ys
∈-++-weakening here = here
∈-++-weakening (there p) = there (∈-++-weakening p)

∈-trans : ∀ {ℓ} {A : Set ℓ} {x y : A} {xs : List A} → x ∈ y , xs → y ∈ xs → x ∈ xs
∈-trans here           y∈xs = y∈xs
∈-trans (there x∈y,xs) y∈xs = x∈y,xs

-- The Derivability Judgement
infix 3 _⊢_[_]
data _⊢_[_] : Context → Judgement → (List Rule) → Set₁ where
    here  : ∀ {  J Γ R  }                 → J , Γ ⊢ J [ R ]
    there : ∀ {x J Γ R  } → Γ ⊢ J [ R ]   → x , Γ ⊢ J [ R ]
    legit : ∀ {  J Γ R} {r : Rule} → r ∈ R → r Γ J → Γ ⊢ J [ R ]

-- _⊢_[_] is "stable" under rule expansion
-- i.e. if Γ ⊢R J then Γ ⊢R∪R′ J
⊢-stable : ∀ {J Γ R R'} → Γ ⊢ J [ R ] → Γ ⊢ J [ R ++ R' ]
⊢-stable here = here
⊢-stable (there p) = there (⊢-stable p)
⊢-stable (legit ∃rule ok) = legit (∈-++-weakening ∃rule) ok

-- Reflexivity: Every judgment is a consequence of itself: J , Γ ⊢ J.
--              Each hypothesis justifies itself as conclusion.
⊢-refl : ∀ {R Γ J} → J , Γ ⊢ J [ R ]
⊢-refl = here

-- Weakening:   If Γ ⊢ J, then K, Γ ⊢ J.
--              Entailment is not influenced by un-exercised options.
⊢-weakening : ∀ {R Γ J K} → Γ ⊢ J [ R ] → K , Γ ⊢ J [ R ]
⊢-weakening Γ⊢J = there Γ⊢J

-- Transitivity: If Γ, K ⊢ J and Γ ⊢ K, then Γ ⊢ J. If we replace an axiom by a
--               derivation of it, the result is a derivation of its consequent
--               without that hypothesis.
⊢-trans : ∀ {R Γ J K} → K , Γ ⊢ J [ R ] → Γ ⊢ K [ R ] → Γ ⊢ J [ R ]
⊢-trans here              Γ⊢K = Γ⊢K
⊢-trans (there p)         Γ⊢K = p
⊢-trans (legit here ok) Γ⊢K = {!   !}
⊢-trans (legit (there ∈rules) ok) Γ⊢K = {!   !}
-- ⊢-trans here          Γ⊢K = Γ⊢K
-- ⊢-trans (there K,Γ⊢J) Γ⊢K = K,Γ⊢J

-- The Admissibility Judgement
-- Γ ⊨R J , is a weaker form of hypothetical judgment stating that ⊢R Γ implies ⊢R J
_⊨_[_] : Judgement → Judgement → (List Rule) → Set₁
Γ ⊨ J [ R ] = [] ⊢ Γ [ R ] → [] ⊢ J [ R ]

-- If Γ ⊢R J, then Γ |=R J.

⊢⇒⊨ : ∀ R Γ J → Γ ⊢ J [ R ] → ∀ γ → γ ∈ Γ → γ ⊨ J [ R ]
⊢⇒⊨ R Γ J Γ⊢J γ ∈Γ = {!   !}
