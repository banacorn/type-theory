module E where

open import Data.String
open import Data.Nat

data Typ : Set where
    Num : Typ
    Str : Typ

data Exp : Set where
    var : String → Exp
    num : ℕ → Exp
    str : String → Exp
    plus : Exp → Exp → Exp
    times : Exp → Exp → Exp
    cat : Exp → Exp → Exp
    len : Exp → Exp
    lass : Exp → Exp
