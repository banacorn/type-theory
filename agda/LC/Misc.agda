module LC.Misc where

open import Size
open import Function

-- http://www2.tcs.ifi.lmu.de/~abel/talkIHP14.pdf
-- Coinduction in Agda using Copatterns and Sized Types
mutual
    -- ♯_ : ∀ {a} {A : Set a} → A → ∞ A
    -- ♭  : ∀ {a} {A : Set a} → ∞ A → A

    data Delay (A : Set) {i : Size} : Set where
        now   :        A → Delay A  -- something ready to be taken out
        later : ∞Delay A → Delay A

    -- force : ∀ {A i} → ∞Delay A i → {j : Size< i} → Delay A j
    record ∞Delay (A : Set) {i : Size} : Set where
        coinductive
        constructor delay
        field
            force : {j : Size< i} → Delay A {j}

open Delay
open ∞Delay


open import Data.Nat
open import Data.Fin
open import Data.Vec using (Vec; lookup; _∷_)

data Term (n : ℕ) : Set where
    var : (x : Fin n)        → Term n
    abs : (t : Term (suc n)) → Term n
    app : (r s : Term n)     → Term n


mutual
    record Value : Set where
        inductive
        constructor closure
        field
            {n} : ℕ
            body : Term (suc n) -- greater than 0
            env : Env n
    Env = Vec Value

-- non-terminating computation
forever : ∀ {A} → ∞Delay A
force forever = later forever

mutual
    _>>=_ : ∀ {A B} → Delay A → (A → Delay B) → Delay B
    now x   >>= f = f x
    later x >>= f = later (x >>=∞ f)        -- sine die

    _>>=∞_ : ∀ {A B} → ∞Delay A → (A → Delay B) → ∞Delay B
    force (x >>=∞ f) = (force x) >>= f


mutual
    apply : Delay Value → Delay Value → Delay Value
    apply x? y? =
        x? >>= λ x →
        y? >>= λ y →
        later (∞apply x y)


    ∞apply : Value → Value → ∞Delay Value
    force (∞apply (closure body ρ) v) = ⟦ body ⟧ (v ∷ ρ)
    -- apply /(closure body ρ) v = ⟦ body ⟧ (v ∷ ρ)

    ⟦_⟧_ : ∀ {n} → Term n → Env n → Delay Value
    ⟦ var x ⟧ ρ = now (lookup x ρ) --  lookup x ρ
    ⟦ abs t ⟧ ρ = now (closure t ρ) -- closure t ρ
    ⟦ app r s ⟧ ρ = apply (⟦ r ⟧ ρ) {!   !} -- apply (⟦ r ⟧ ρ) (⟦ s ⟧ ρ)
