open import Relation.Binary

module Membership.DecSetoid {c ℓ} (A : DecSetoid c ℓ) where

open DecSetoid A

open import Relation.Nullary
open import Relation.Nullary.Negation using (contradiction)
open import Data.List

open import Membership.Core {c} {ℓ} Carrier _≈_ isEquivalence public

∈?-lemma : ∀ {x x' xs} → ¬ (x ≈ x') → ¬ (x ∈ xs) → ¬ (x ∈ x' ∷ xs)
∈?-lemma ¬eq ¬in (here p)  = contradiction p ¬eq
∈?-lemma ¬eq ¬in (there p) = contradiction p ¬in

infix 3 _∈?_
_∈?_ : (x : Carrier) → (xs : List Carrier) → Dec (x ∈ xs)
x ∈? [] = no (λ ())
x ∈? (x' ∷ xs) with x ≟ x'
x ∈? (x' ∷ xs) | yes eq = yes (here eq)
x ∈? (x' ∷ xs) | no ¬eq with x ∈? xs
x ∈? (x' ∷ xs) | no ¬eq | yes p = yes (there p)
x ∈? (x' ∷ xs) | no ¬eq | no ¬p = no (∈?-lemma ¬eq ¬p)
