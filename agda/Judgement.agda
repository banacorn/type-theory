module Judgement where

open import Data.List
open import Data.Unit using (⊤)



data Variable : Set where

infix 4 _∶_
data Judgement : Set where
    _∶_ : Variable → Variable → Judgement
    _≡_∶_ : Variable → Variable → Variable → Judgement

Context : Set
Context = List Judgement

import Membership
open Membership Judgement

infix 3 _⊢_
_⊢_ : Context → Judgement → Set
Γ ⊢ J = J ∈ Γ

data CTX : Context → Set where
    ctx-EMP : CTX []
    ctx-EXT : ∀ {Γ A 𝒰 x} → Γ ⊢ A ∶ 𝒰 → CTX ((x ∶ A) ∷ Γ)

data Structural : Set where
    Vble : ∀ {Γ x A} → CTX Γ → Γ ⊢ x ∶ A
