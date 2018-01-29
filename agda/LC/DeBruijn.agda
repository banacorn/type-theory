module LC.DeBruijn where

open import Data.Nat
open import Data.Empty
open import Relation.Nullary

-- the index `level` denotes the number of `abs`, i.e., the least binding number
-- for a variable to be free
-- data Term : (#abs : ℕ) → Set where
--     var : ℕ → Term 0
--     abs : ∀ {n} → Term n → Term (suc n)
--     app : ∀ {m n o} → (body : Term m) → (term : Term n) → Term o

data Term : Set where
    var : ℕ → Term
    abs : Term → Term
    app : Term → Term → Term



decrease-bound : ℕ → Term → Term
decrease-bound lvl (var x) with suc lvl ≤? x
decrease-bound lvl (var zero)    | yes ()
decrease-bound lvl (var (suc x)) | yes p = var x
decrease-bound lvl (var x)       | no ¬p = var x
decrease-bound lvl (abs term) = abs (decrease-bound (suc lvl) term)
decrease-bound lvl (app body sbst) = app
    (decrease-bound lvl body) (decrease-bound lvl sbst)

increase-bound : ℕ → Term → Term
increase-bound lvl (var x) with suc lvl ≤? x
increase-bound lvl (var zero)    | yes ()
increase-bound lvl (var (suc x)) | yes p = var (suc (suc x))
increase-bound lvl (var x)       | no ¬p = var x
increase-bound lvl (abs term) = abs (increase-bound (suc lvl) term)
increase-bound lvl (app body sbst) = app
    (increase-bound lvl body) (increase-bound lvl sbst)

module Properties where

    open import Relation.Nullary.Negation
    open import Relation.Binary.PropositionalEquality
    open import Data.Nat.Properties

    decrease-increase-bound : (lvl : ℕ) → (term : Term) → decrease-bound lvl (increase-bound lvl term) ≡ term
    decrease-increase-bound lvl (var zero) = refl
    decrease-increase-bound lvl (var (suc x)) with lvl ≤? x
    decrease-increase-bound lvl (var (suc x)) | yes p with lvl ≤? suc x
    decrease-increase-bound lvl (var (suc x)) | yes p | yes q = refl
    decrease-increase-bound lvl (var (suc x)) | yes p | no ¬q = ⊥-elim (¬q (≤-step p))
    decrease-increase-bound lvl (var (suc x)) | no ¬p with lvl ≤? x
    decrease-increase-bound lvl (var (suc x)) | no ¬p | yes q = ⊥-elim (¬p q)
    decrease-increase-bound lvl (var (suc x)) | no ¬p | no ¬q = refl
    decrease-increase-bound lvl (abs term) = cong abs
        (decrease-increase-bound (suc lvl) term)
    decrease-increase-bound lvl (app body term) = cong₂ app
        (decrease-increase-bound lvl body)
        (decrease-increase-bound lvl term)

substitute : (lvl : ℕ) → (body term : Term) → Term
substitute lvl (var x) term with lvl ≟ x
substitute lvl (var x) term | yes p = term
substitute lvl (var x) term | no ¬p = var x
substitute lvl (abs body) term = substitute (suc lvl) body (increase-bound (suc lvl) term)
substitute lvl (app body sbst) term = app (substitute lvl body term) (substitute lvl sbst term)

module Test where

    term0 : Term
    term0 = var 0

    term1 : Term
    term1 = var 6

    id-body : Term
    id-body = abs (var 0)

    3-deep : Term
    3-deep = abs (abs (abs (var 3)))

    test : ℕ → Term
    test n = substitute 0 3-deep (var n)

open import Data.Maybe

β-redex-in-head : Term → Maybe Term
β-redex-in-head (var x) = nothing
β-redex-in-head (abs term) = β-redex-in-head term
β-redex-in-head (app (var x) term) = nothing
β-redex-in-head (app (abs body) term) = just {!   !}
β-redex-in-head (app (app body term') term) = {!   !}

-- β-redex-in-head : Term → Bool
-- β-redex-in-head (var x) = false
-- β-redex-in-head (abs term) = β-redex-in-head term
-- β-redex-in-head (app (var x) term) = false
-- β-redex-in-head (app (abs body) term) = true
-- β-redex-in-head (app (app body term₁) term₀) = β-redex-in-head (app body term₁)

β-reduce : Term → Term
β-reduce (var x) = var x
β-reduce (abs term) = abs (β-reduce term)
β-reduce (app (var x) term) = var x
β-reduce (app (abs body) term) = substitute {!   !} {!   !} {!   !}
β-reduce (app (app body term') term) = {!   !}


-- β-reduce (app (var x) term) = var x
-- β-reduce (app (abs body) term) = {!   !}
-- β-reduce (app (app body sbst) term) = {!   !}

-- substitute : ∀ {b t} → (lvl : ℕ) → (body : Term b) → (term : Term t)
--     → Term {!   !}
--     -- → Term (substitute-#abs lvl body term)
-- substitute {b} lvl (var x) term with lvl ≟ x
-- substitute {b} lvl (var x) term | yes p = term
-- substitute {b} lvl (var x) term | no ¬p = var x
-- substitute lvl (abs body) term =
--     substitute (suc lvl) body term
-- substitute lvl (app body t) term =
--     app (substitute lvl body {! term  !}) (substitute lvl t term)


-- substitute : Term → Term → Term
-- substitute (var zero) term = term
-- substitute (var (suc x)) term = var (suc x)
-- substitute (abs body) term = {!   !}
-- substitute (app body t) term = {!   !}
--
-- -- reduce terms in the normal order
-- β-reduce : Term → Term
-- β-reduce (var x) = var x
-- β-reduce (abs term) = abs (β-reduce term)
-- β-reduce (app (var x) term) = app (var x) term
-- β-reduce (app (abs body) term) = substitute body term
-- β-reduce (app (app body t) term) = app (app body t) term

-- (λ λ 4 2 (λ 1 3)) (λ 5 1)
-- a : Term 6
-- a = app
--         (abs (app
--                 (app
--                     (abs (var 4))
--                     (var 2))
--                 (abs (app
--                     (var 1)
--                     (var 3)))))
--         (abs (app
--             (var 5)
--             (var 1)))

-- β : ∀ {n} → Term n → ℕ
-- β {n} (var x) = n
-- β {suc n} (abs t) = suc (β t)
-- β (app body term) with β body
-- ... | t = suc t
-- decrease-bound : Term → Term
-- decrease-bound (var x) = {!   !}
-- decrease-bound (abs t) = {!   !}
-- decrease-bound (app s t) = {!   !}
-- --
-- substitute : ∀ {m n} → (body : Term m) → (part : Term n) → Term (β body)
-- substitute (var v) x = var v
-- substitute (abs body) x = {!   !}
-- substitute (app body part) x = {!   !}

-- β-reduce : ∀ {n} → (term : Term n) → Term (β term)
-- β-reduce (var x) = var x
-- β-reduce (abs term) = abs (β-reduce term)
-- β-reduce (app body term) with β-reduce body
-- ... | t = {! t  !}
-- β-reduce (app (var x) term) = app (var x) (β-reduce term)
-- β-reduce (app (abs body) term) = {!   !}
-- β-reduce (app (app body termᵢ) termₒ) = β-reduce (app {! β-reduce  !} {!   !})

-- β-reduce : ∀ {n} → Term n → Term n
-- β-reduce (var x) = var x
-- β-reduce (abs t) = abs (β-reduce t)
-- β-reduce (app (var v) t) = {! var v  !}
-- β-reduce (app (abs s) t) = {!   !}
-- β-reduce (app (app s s₁) t) = {!   !}

-- null : Term 2
-- null = abs (abs (var 0))

-- ein : Term 2
-- ein = abs (abs (app (var 0) (var 0)))
