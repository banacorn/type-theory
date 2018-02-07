module Membership {c} (A : Set c) where

open import Relation.Binary.PropositionalEquality using (_≡_; isEquivalence)

open import Membership.Core {c} {c} A _≡_ isEquivalence public
