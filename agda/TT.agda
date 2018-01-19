module TT where

-- open import Relation.Binary.PropositionalEquality using (_≡_; refl)
-- open import Data.List renaming (_∷_ to _,_)

data Judgement (V T : Set) : Set where
    -- typing judgement
    _∶_ : V → T → Judgement V T
    -- equality judgement
    _:≡_ : V → V → Judgement V T

open import Context Judgement

data _⊢[_]_ {V T : Set} : (Γ R : Context V T) (J : Judgement V T) → Set where
    Axiom : ∀ R J → [] ⊢[ R ] J
    Proper : ∀ Γ R J → J ∈ (Γ ++ R) → Γ ⊢[ R ] J

⊢-stable : ∀ {V T} → (Γ R R' : Context V T) → (J : Judgement V T) → Γ ⊢[ R ] J → Γ ⊢[ R ++ R' ] J
⊢-stable {V} {T} .[] R R' J (Axiom .R .J)       = Axiom (R ++ R') J
⊢-stable {V} {T} Γ   R R' J (Proper .Γ .R .J x) = Proper Γ (R ++ R') J
    {!  ∈-++ J (Γ ++ R) R' x   !}
    -- Proper Γ (R ++ R') J {! ∈-++ J (Γ ++ R) R' x !}
