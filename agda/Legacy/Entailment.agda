open import Relation.Binary

module Entailment {c ℓ} (JudgementDecSetoid : DecSetoid c ℓ) where

open import Data.List public
open import Level
open import Relation.Nullary


open DecSetoid JudgementDecSetoid renaming (Carrier to Judgement)

Context : Set c
Context = List Judgement

Rule : Set (suc zero ⊔ c)
Rule = Context → Judgement → Set

open import Data.Product
import DecSetoidMembership
open DecSetoidMembership JudgementDecSetoid

import Membership
open Membership Rule using () renaming (_∈_ to _∈ᵣ_; _⊆_ to _⊆ᵣ_)
module R = Membership Rule

record Legit (Γ : Context) (R : List Rule) (J : Judgement) : Set (suc zero ⊔ c ⊔ ℓ) where
    constructor lgt
    field
        subcontext : ∃[ Δ ] (Δ ⊆ Γ)
        rule       : ∃[ r ] (r ∈ᵣ R)
        legit      : (proj₁ rule) (proj₁ subcontext) J

        map' : ∀ {Δ Δ' R R' J} → Δ ⊆ Δ' → R ⊆ᵣ R' → legit Δ R J → legit Δ' R' J

bimap : ∀ {Γ Γ' R R' J} → Γ ⊆ Γ' → R ⊆ᵣ R' → Legit Γ R J → Legit Γ' R' J
bimap Γ⊆Γ' R⊆R' L = record
    { subcontext = proj₁ subcontext , ⊆-trans (proj₂ subcontext) Γ⊆Γ'
    ; rule = proj₁ rule , R⊆R' (proj₂ rule)
    ; legit = legit
    }
    where open Legit L



mapContext : ∀ {Γ Γ' R J} → Γ ⊆ Γ' → Legit Γ R J → Legit Γ' R J
mapContext Γ⊆Γ' = bimap Γ⊆Γ' R.⊆-refl

mapRules : ∀ {Γ R R' J} → R ⊆ᵣ R' → Legit Γ R J → Legit Γ R' J
mapRules R⊆R' = bimap ⊆-refl R⊆R'

Legit-Context-weakening : ∀ {Γ K R J} → Legit Γ R J → Legit (K ∷ Γ) R J
Legit-Context-weakening = mapContext there

Legit-Context-trans : ∀ {Γ K R J} → K ∈ Γ → Legit (K ∷ Γ) R J → Legit Γ R J
Legit-Context-trans K∈Γ = mapContext (nub K∈Γ)

Legit-trans : ∀ {R Γ K J} → Legit Γ R K → Legit (K ∷ Γ) R J → Legit Γ R J
Legit-trans {R} {Γ} {K} {J} Γ⊢K K∷Γ⊢J with K ∈? (proj₁ (Legit.subcontext Γ⊢K))
Legit-trans {R} {Γ} {K} {J} Γ⊢K K∷Γ⊢J | yes p = {!   !}
    where
        open Legit

        Δ : List Judgement
        Δ = proj₁ (Legit.subcontext Γ⊢K)

        P0 : K ∷ Δ ⊆ Δ
        P0 = nub {Δ} {K} p
Legit-trans {R} {Γ} {K} {J} Γ⊢K K∷Γ⊢J | no ¬p = {!   !}

        -- P0 : K  :
        -- nub {proj₁ (Legit.subcontext Γ⊢K)} {K} p
-- Legit-trans {R} {Γ} {K} {J} Γ⊢K K,Γ⊢J = lgt (subctx , subctx⊆Γ) (rule K,Γ⊢J) (legit K,Γ⊢J)
    --
    --     -- K ∷ Γ
    --     subctx : List Judgement
    --     subctx =  proj₁ (subcontext K,Γ⊢J) -- {!  !} --
    --
    --     subctx⊆Γ : subctx ⊆ Γ
    --     subctx⊆Γ {x} (here {j} {js}) = {!   !}
    --     subctx⊆Γ {x} (there x∈subctx) = {!   !}

        -- open Membership
-- Legit-trans {R} {Γ} {K} {J} Γ⊢K K,Γ⊢J with Legit.subcontext Γ⊢K
-- Legit-trans {R} {Γ} {K} {J} Γ⊢K K,Γ⊢J | subctx , subctx⊆Γ = {!   !}

-- Legit Γ R J
-- Legit (K ∷ Γ) R J
-- Legit Γ R K ->  Legit (K ∷ Γ) R K

-- Legit-trans {R} {Γ} {K} {J}
--     (lgt ([] , subctx-L) rule-L legit-L)
--     (lgt ([] , subctx-M) rule-M legit-M)
--     = lgt ([] , subctx-L) rule-M legit-M
-- Legit-trans {R} {Γ} {K} {J}
--     (lgt ([] , subctx-L) rule-L legit-L)
--     (lgt (y ∷ ys , subctx-M) rule-M legit-M)
--     = mapContext {!   !} (lgt (y ∷ ys , subctx-M) rule-M legit-M) -- mapContext {!   !} {!   !}
-- Legit-trans {R} {Γ} {K} {J} (lgt (x ∷ xs , subctx-L) rule-L legit-L) (lgt ([] , subctx-M) rule-M legit-M) = {!   !}
-- Legit-trans {R} {Γ} {K} {J} (lgt (x ∷ xs , subctx-L) rule-L legit-L) (lgt (y ∷ ys , subctx-M) rule-M legit-M) = {!   !}

Legit-Rules-++-weakening : ∀ {Γ R R' J} → Legit Γ R J → Legit Γ (R ++ R') J
Legit-Rules-++-weakening = mapRules (R.append _)

-- The Derivability Judgement
infix 3 _⊢_[_]
data _⊢_[_] : Context → Judgement → (List Rule) → Set₁ where
    in-context : ∀ {J Γ R} → J ∈ Γ → Γ ⊢ J [ R ]
    by-rules   : ∀ {J Γ R} → Legit Γ R J → Γ ⊢ J [ R ]

-- _⊢_[_] is "stable" under rule expansion
-- i.e. if Γ ⊢R J then Γ ⊢R∪R′ J
⊢-stable : ∀ {J Γ R R'} → Γ ⊢ J [ R ] → Γ ⊢ J [ R ++ R' ]
⊢-stable (in-context ∈Context) = in-context ∈Context
⊢-stable (by-rules L) = by-rules (Legit-Rules-++-weakening L)

-- Reflexivity: Every judgment is a consequence of itself: J , Γ ⊢ J.
--              Each hypothesis justifies itself as conclusion.
⊢-refl : ∀ {R Γ J} → J ∷ Γ ⊢ J [ R ]
⊢-refl = in-context (here {!   !})

-- Weakening:   If Γ ⊢ J, then K, Γ ⊢ J.
--              Entailment is not influenced by un-exercised options.
⊢-weakening : ∀ {R Γ J K} → Γ ⊢ J [ R ] → K ∷ Γ ⊢ J [ R ]
⊢-weakening (in-context ∈Context) = in-context (there ∈Context)
⊢-weakening (by-rules L) = by-rules (Legit-Context-weakening L)

-- ⊢-trans : ∀ {R Γ J K} → K ∷ Γ ⊢ J [ R ] → Γ ⊢ K [ R ] → Γ ⊢ J [ R ]

-- Transitivity: If Γ, K ⊢ J and Γ ⊢ K, then Γ ⊢ J. If we replace an axiom by a
--               derivation of it, the result is a derivation of its consequent
--               without that hypothesis.
⊢-trans : ∀ {R Γ J K} → K ∷ Γ ⊢ J [ R ] → Γ ⊢ K [ R ] → Γ ⊢ J [ R ]
⊢-trans (in-context (here p)) Γ⊢K = {!   !}
⊢-trans (in-context (there ∈Context)) Γ⊢K = in-context ∈Context
⊢-trans (by-rules L) (in-context K∈Γ) = by-rules (mapContext (nub K∈Γ) L)
⊢-trans {R} {Γ} {J} {K} (by-rules L) (by-rules M)  = by-rules {!   !}
    -- by-rules (Legit-Context-trans {!   !} L)
    -- where
    --     K∈Γ : K ∈ Γ
    --     K∈Γ = {!   !} --subcontext⊆Γ K {!   !}
-- ⊢-trans {R} {[]} {J} {K} (by-rules L) (by-rules M) = {! rule M  !}
--     where
--         open Legit
-- ⊢-trans {R} {γ ∷ Γ} {J} {K} (by-rules L) (by-rules M) = {! ⊢-trans ? (by-rules L)  !}
-- (record
--      { subcontext = A.subcontext
--      ; subcontext⊆Γ = λ a x → B.subcontext⊆Γ a {!   !}
--      ; rule = A.rule
--      ; rule∈R = A.rule∈R
--      ; legit = A.legit
--      })
--      where
--          module A = Legit A
--          module B = Legit B
    -- by-rules (record
     -- { subcontext = subcontext
     -- ; subcontext⊆Γ = {!subcontext⊆Γ   !}
     -- ; rule = {!   !}
     -- ; rule∈R = {!   !}
     -- ; legit = {!   !}
     -- })
     -- where open Legit legit
-- ⊢-trans here              Γ⊢K = Γ⊢K
-- ⊢-trans (there p)         Γ⊢K = p
-- ⊢-trans (legit here ok) Γ⊢K = {!   !}
-- ⊢-trans (legit (there ∈rules) ok) Γ⊢K = {!   !}
-- -- ⊢-trans here          Γ⊢K = Γ⊢K
-- -- ⊢-trans (there K,Γ⊢J) Γ⊢K = K,Γ⊢J
--
-- -- The Admissibility Judgement
-- -- Γ ⊨R J , is a weaker form of hypothetical judgment stating that ⊢R Γ implies ⊢R J
-- _⊨_[_] : Judgement → Judgement → (List Rule) → Set₁
-- Γ ⊨ J [ R ] = [] ⊢ Γ [ R ] → [] ⊢ J [ R ]
--
-- -- If Γ ⊢R J, then Γ |=R J.
--
-- ⊢⇒⊨ : ∀ R Γ J → Γ ⊢ J [ R ] → ∀ γ → γ ∈ Γ → γ ⊨ J [ R ]
-- ⊢⇒⊨ R Γ J Γ⊢J γ ∈Γ = {!   !}
