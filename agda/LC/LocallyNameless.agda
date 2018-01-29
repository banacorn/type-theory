module LC.LocallyNameless where

open import Data.Nat
open import Data.String

data Term : Set where
    bvar : ℕ → Term
    fvar : String → Term
    abs : Term → Term
    app : Term → Term → Term

a : Term
a = abs (app (abs (app (bvar 0) (bvar 1))) (bvar 0))

b : Term
b =      app (abs (app (bvar 0) (fvar "x"))) (fvar "x")
