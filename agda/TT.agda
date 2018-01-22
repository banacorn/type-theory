module TT where

-- open import Relation.Binary.PropositionalEquality using (_≡_; refl)
-- open import Data.List renaming (_∷_ to _,_)

data Judgement (V T : Set) : Set where
    -- typing judgement
    _∶_ : V → T → Judgement V T
    -- equality judgement
    _:≡_ : V → V → Judgement V T

open import Context Judgement

infix 3 _⊢[_]_

data _⊢[_]_ {V T : Set} : (Γ R : Context V T) (J : Judgement V T) → Set where
    Axiom : ∀ R J → J ∈ R → [] ⊢[ R ] J
    Proper : ∀ Γ R J → J ∈ (Γ ++ R) → Γ ⊢[ R ] J

-- Derivability is stable under extension with new rules.
⊢-stable : ∀ {V T} → (Γ R R' : Context V T) → (J : Judgement V T)
    → Γ ⊢[ R ]       J
    → Γ ⊢[ R ++ R' ] J
⊢-stable {V} {T} .[] R R' J (Axiom .R .J J∈)      = Axiom (R ++ R') J (append R' J∈)
    where open Inc J
⊢-stable {V} {T} Γ   R R' J (Proper .Γ .R .J J∈) = Proper Γ (R ++ R') J
    ((begin
        Γ ++ R
    ≤⟨ append R' ⟩
        (Γ ++ R) ++ R'
    ≈⟨ propEq (assoc Γ R R') ⟩
        Γ ++ R ++ R'
    ∎) J∈)
    where
        open Inc J



-- Reflexivity: Every judgment is a consequence of itself: J , Γ ⊢R J.
--              Each hypothesis justifies itself as conclusion.
⊢-refl : ∀ {V T} → (Γ R : Context V T) → (J : Judgement V T) → J , Γ ⊢[ R ] J
⊢-refl Γ R J = Proper (J , Γ) R J here

-- Weakening:   If Γ ⊢R J, then K, Γ ⊢R J.
--              Entailment is not influenced by un-exercised options.
⊢-weakening : ∀ {V T} → (Γ R : Context V T) → (J K : Judgement V T) → Γ ⊢[ R ] J → K , Γ ⊢[ R ] J
⊢-weakening .[] R J K (Axiom .R .J J∈) = Proper (K , []) R J (prepend (K , []) J∈)
    where open Inc J
⊢-weakening Γ R J K (Proper .Γ .R .J J∈) = Proper (K , Γ) R J (there J∈)
    where open Inc J

-- Transitivity: If Γ, K ⊢R J and Γ ⊢R K, then Γ ⊢R J. If we replace an axiom by a derivation of it,
--               the result is a derivation of its consequent without that hypothesis.
⊢-trans : ∀ {V T} → (Γ R : Context V T) → (J K : Judgement V T)
    → K , Γ ⊢[ R ] J
    →     Γ ⊢[ R ] K
    →     Γ ⊢[ R ] J
⊢-trans .[] R J K (Proper .(K , []) .R .J P) (Axiom .R .K Q) = Axiom R J (nub J K R P Q)
⊢-trans Γ R J K (Proper .(K , Γ) .R .J P) (Proper .Γ .R .K Q) = Proper Γ R J (nub J K (Γ ++ R) P Q)
