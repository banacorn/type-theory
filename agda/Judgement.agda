module Judgement where

open import Data.List
open import Data.Unit using (⊤)



data Variable : Set where
data Type : Set where
data Term : Set where
    var : Variable → Term


infix 100 _∶_
data Judgement : Set where
    _∶𝒰   : Type → Judgement
    _∶_   : Term → Type → Judgement
    _≡_∶_ : Term → Term → Type → Judgement
    _≡_∶𝒰 : Type → Type → Judgement

Context : Set
Context = List Judgement

open import Membership Judgement

infix 200 _[_/_]
_[_/_] : Term → Term → Variable → Term
expr [ sbst / x ] = {!   !}

infix 200 _[_/_]'
_[_/_]' : Context → Term → Variable → Context
expr [ sbst / x ]' = {!   !}

infix 200 _[_/_]ᵗ
_[_/_]ᵗ : Type → Term → Variable → Type
expr [ sbst / x ]ᵗ = {!   !}



mutual
    data CTX : Context → Set where
        ctx-EMP : CTX []
        ctx-EXT : ∀ {Γ A 𝒰 x} → Γ ⊢ A ∶𝒰 → CTX ((x ∶ A) ∷ Γ)

    infix 3 _⊢_
    data _⊢_ : Context → Judgement → Set where
        in-context : ∀ {J Γ} → J ∈ Γ → Γ ⊢ J

        Vble : ∀ {Γ A} {x : Variable} → CTX Γ → Γ ⊢ var x ∶ A

        Subst₁ : ∀ {Γ Δ A B a b} {x : Variable}
            →                             Γ ⊢ a           ∶ A
            → Δ            ++ var x ∶ A ∷ Γ ⊢ b           ∶ B
            → Δ [ a / x ]' ++             Γ ⊢ b [ a / x ] ∶ B [ a / x ]ᵗ

        Wkg₁ : ∀ {Γ Δ 𝒰 A B b} {x : Variable}
            →                  Γ ⊢ A ∶𝒰
            → Δ ++             Γ ⊢ b ∶ B
            → Δ ++ var x ∶ A ∷ Γ ⊢ b ∶ B

        Subst₂ : ∀ {Γ Δ A B a b c} {x : Variable}
            →                             Γ ⊢ a                         ∶ A
            → Δ            ++ var x ∶ A ∷ Γ ⊢ b           ≡ c           ∶ B
            → Δ [ a / x ]' ++             Γ ⊢ b [ a / x ] ≡ c [ a / x ] ∶ B [ a / x ]ᵗ

        Wkg₂ : ∀ {Γ Δ 𝒰 A B b c} {x : Variable}
            →                  Γ ⊢     A ∶𝒰
            → Δ ++             Γ ⊢ b ≡ c ∶ B
            → Δ ++ var x ∶ A ∷ Γ ⊢ b ≡ c ∶ B

        ≡-refl : ∀ {Γ A a}
            → Γ ⊢ a ∶ A
            → Γ ⊢ a ≡ a ∶ A

        ≡-sym : ∀ {Γ A a b}
            → Γ ⊢ a ≡ b ∶ A
            → Γ ⊢ b ≡ a ∶ A

        ≡-trans : ∀ {Γ A a b c}
            → Γ ⊢ a ≡ b ∶ A
            → Γ ⊢ b ≡ c ∶ A
            → Γ ⊢ a ≡ c ∶ A

        ≡-transport₁ : ∀ {Γ A B a}
            → Γ ⊢ a ∶ A
            → Γ ⊢ A ≡ B ∶𝒰
            → Γ ⊢ a ∶ B

        ≡-transport₂ : ∀ {Γ A B a b}
            → Γ ⊢ a ≡ b ∶ A
            → Γ ⊢ A ≡ B ∶𝒰
            → Γ ⊢ a ≡ b ∶ B

            -- Γ⊢A:Ui Γ,x:A⊢B:Ui Γ,x:A⊢b≡b′ :B Π-INTRO-EQ Γ ⊢ λx.b ≡ λx.b′ : ∏(x:A)B


            -- Γ ⊢ A : Ui Γ, ∆ ⊢ b : B Wkg Γ,x:A,∆ ⊢ b : B 1
            -- Γ ⊢ A : Ui Γ, ∆ ⊢ b ≡ c : B Wkg Γ, x:A, ∆ ⊢ b ≡ c : B 2
            --   Γ, ∆[a/x] ⊢ b[a/x] ≡ c[a/x] : B[a/x] 2
    -- by-rule : ∀ {Γ J K R} → Γ ⊢ J [ R ] → Γ ⊢ K [ R ] → Γ ⊢ R J K [ R ]

-- infix 3 _⊢_
-- _⊢_ : Context → Judgement → Set
-- Γ ⊢ J = J ∈ Γ
--
-- data CTX : Context → Set where
--     ctx-EMP : CTX []
--     ctx-EXT : ∀ {Γ A 𝒰 x} → Γ ⊢ A ∶ 𝒰 → CTX ((x ∶ A) ∷ Γ)

-- data Structural : Set where
--     Vble : ∀ {Γ x A} → CTX Γ → Γ ⊢ x ∶ A → Structural
--     subst₁ : ∀ {Γ Δ a b x A B} → Γ ⊢ a ∶ A
