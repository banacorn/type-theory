module Judgement where

open import Data.List
open import Data.Product hiding (map)
open import Data.Nat
open import Data.String using (String) renaming (_≟_ to _≟str_)
open import Relation.Nullary
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PE using (_≡_)



-- data Variable : Set where

Variable : Set
Variable = String

data Term : Set where
    var : String → Term


infix 100 _∶_ _≣_∶_ _∶_𝒰 _≣_∶_𝒰
data Judgement : Set where
    _∶_     : (a A : Term) → Judgement
    _≣_∶_   : (a b A : Term) → Judgement
    _∶_𝒰   : (A : Term) → (𝒾 : ℕ) → Judgement
    _≣_∶_𝒰 : (A B : Term) → (𝒾 : ℕ) → Judgement

Context : Set
Context = List Judgement

open import Membership Judgement

infix 200 _[_/_]
_[_/_] : Term → Term → Variable → Term
var x' [ expr / x ] with x' ≟str x
var x' [ expr / x ] | yes p = expr
var x' [ expr / x ] | no ¬p = var x'

_[_/_]J : Judgement → Term → Variable → Judgement
(    a ∶ A)   [ expr / x ]J = a [ expr / x ] ∶ A [ expr / x ]
(a ≣ b ∶ A)   [ expr / x ]J = a [ expr / x ] ≣ b [ expr / x ] ∶ A [ expr / x ]
(    A ∶ 𝒾 𝒰) [ expr / x ]J = A [ expr / x ] ∶ 𝒾 𝒰
(A ≣ B ∶ 𝒾 𝒰) [ expr / x ]J = A [ expr / x ] ≣ B [ expr / x ] ∶ 𝒾 𝒰

infix 200 _[_/_]'
_[_/_]' : Context → Term → Variable → Context
context [ expr / x ]' = map (λ w → w [ expr / x ]J) context

++-context-substitution : ∀ {e x} Γ Δ → (Γ ++ Δ) [ e / x ]' ≋ Γ [ e / x ]' ++ Δ [ e / x ]'
++-context-substitution {e} {x} Γ Δ = ≡→≋ (map-++-commute (λ w → w [ e / x ]J) Γ Δ)
    where
        open import Data.List.Properties using (map-++-commute)

sbst-lemma210 : ∀ a x → a ≡ a [ a / x ]
sbst-lemma210 (var x') x with x ≟str x | x' ≟str x
sbst-lemma210 (var x') x | yes p | yes q = PE.refl
sbst-lemma210 (var x') x | yes p | no ¬q = PE.refl
sbst-lemma210 (var x') x | no ¬p | yes q = PE.refl
sbst-lemma210 (var x') x | no ¬p | no ¬q = PE.refl

sbst-lemma21 : ∀ A a x → (var x ∶ A) [ a / x ]J ≡ (a ∶ A) [ a / x ]J
sbst-lemma21 A a x with x ≟str x
sbst-lemma21 A a x | yes p = PE.cong (λ w → w ∶ A [ a / x ]) (sbst-lemma210 a x)
sbst-lemma21 A a x | no ¬p = contradiction PE.refl ¬p

judgement-substitution-mono : ∀ Γ J e x → J ∈ Γ → (J [ e / x ]J) ∈ Γ [ e / x ]'
judgement-substitution-mono Γ J e x (here  p) = here  (PE.cong (λ w → w [ e / x ]J) p)
judgement-substitution-mono Γ J e x (there p) = there (judgement-substitution-mono _ J e x p)

context-substitution-mono : ∀ Γ Δ e x → Γ ⊆ Δ → Γ [ e / x ]' ⊆ Δ [ e / x ]'
context-substitution-mono [] Δ e x P ()
context-substitution-mono (J ∷ Γ) Δ e x P (here PE.refl) = judgement-substitution-mono Δ J e x (P (here PE.refl))
context-substitution-mono (J ∷ Γ) Δ e x P (there Q) = context-substitution-mono Γ Δ e x (
    begin
        Γ
    ≤⟨ there ⟩
        J ∷ Γ
    ≤⟨ P ⟩
        Δ
    ∎) Q
-- context-substitution-mono []      Δ a x P = λ ()
-- context-substitution-mono (J ∷ Γ) Δ a x P =
--     begin
--         (J ∷ Γ) [ a / x ]'
--     ≈⟨ ≋-refl ⟩
--         (J [ a / x ]J) ∷ Γ [ a / x ]'
--     ≈⟨ {!   !} ⟩
--         {!   !}
--     ≤⟨ {!  nub P !} ⟩
--         Δ [ a / x ]'
--     ∎

sbst-lemma2 : ∀ Γ A a x → a ∶ A ∈ Γ → (var x ∶ A ∷ Γ) [ a / x ]' ⊆ Γ [ a / x ]'
sbst-lemma2 [] A a x ()
sbst-lemma2 (J ∷ Γ) A a x P =
    begin
        (var x ∶ A ∷ (J ∷ Γ)) [ a / x ]'
    ≈⟨ ≋-refl ⟩
        (var x ∶ A) [ a / x ]J ∷ (J ∷ Γ) [ a / x ]'
    ≈⟨ ≡→≋ (PE.cong (λ p → p ∷ (J ∷ Γ) [ a / x ]') (sbst-lemma21 A a x)) ⟩
        (a ∶ A ∷ J ∷ Γ) [ a / x ]'
    ≤⟨ context-substitution-mono (_ ∶ _ ∷ J ∷ Γ) (J ∷ Γ) a x (nub P) ⟩
        (J ∷ Γ) [ a / x ]'
    ∎


-- sbst-lemma2 (.(a ∶ A) ∷ Γ) A a x (here PE.refl) = {!   !}
-- sbst-lemma2 (J ∷ Γ) A a x (there P) = {!   !}



    -- begin
    --     (var x ∶ A ∷ (J ∷ Γ)) [ a / x ]'
    -- ≈⟨ ≋-refl ⟩
    --     sbstJudgement a x (var x ∶ A) ∷ (J ∷ Γ) [ a / x ]'
    -- ≈⟨ ≡→≋ (PE.cong (λ p → p ∷ (J ∷ Γ) [ a / x ]') (sbst-lemma20 A a x)) ⟩
    --     a ∶ A [ a / x ] ∷ (J ∷ Γ) [ a / x ]'
    -- ≤⟨ {!   !} ⟩
    --     a ∶ A ∷ J ∷ Γ
    -- ≤⟨ nub P ⟩
    --     J ∷ Γ
    -- ∎
-- sbst-lemma2 .(a ∶ A ∷ _) A a x (here PE.refl) = {!   !}
-- sbst-lemma2 .(_ ∷ _) A a x (there P) = {!   !}
    -- where
    --     open
    -- Q , {!   !}
    -- where
    --     Q : (var x ∶ A ∷ Γ) [ a / x ]' ⊆ Γ
    --     Q = {!   !}

mutual
    data CTX : Context → Set where
        ctx-EMP : CTX []
        ctx-EXT : ∀ {Γ 𝒾 A x} → Γ ⊢ A ∶ 𝒾 𝒰 → CTX ((x ∶ A) ∷ Γ)

    infix 3 _⊢_
    data _⊢_ : Context → Judgement → Set where
        in-context : ∀ {J Γ} → J ∈ Γ → Γ ⊢ J

        Vble : ∀ {Γ A} {x : Variable}
            → CTX Γ
            ------------------------------
            → Γ ⊢ var x ∶ A

        -- Wkg₁ : ∀ {Γ Δ 𝒾 A B b} {x : Variable}
        --     →                  Γ ⊢ A ∶ 𝒾 𝒰
        --     → Δ ++             Γ ⊢ b ∶ B
        --     → Δ ++ var x ∶ A ∷ Γ ⊢ b ∶ B
        --
        -- Subst₂ : ∀ {Γ Δ A B a b c} {x : Variable}
        --     →                             Γ ⊢ a                         ∶ A
        --     → Δ            ++ var x ∶ A ∷ Γ ⊢ b           ≡ c           ∶ B
        --     → Δ [ a / x ]' ++             Γ ⊢ b [ a / x ] ≡ c [ a / x ] ∶ B [ a / x ]
        --
        -- Wkg₂ : ∀ {Γ Δ 𝒾 A B b c} {x : Variable}
        --     →                  Γ ⊢     A ∶ 𝒾 𝒰
        --     → Δ ++             Γ ⊢ b ≡ c ∶ B
        --     → Δ ++ var x ∶ A ∷ Γ ⊢ b ≡ c ∶ B

        ≣-refl : ∀ {Γ A a}
            → Γ ⊢ a ∶ A
            ------------------------------
            → Γ ⊢ a ≣ a ∶ A

        ≣-sym : ∀ {Γ A a b}
            → Γ ⊢ a ≣ b ∶ A
            ------------------------------
            → Γ ⊢ b ≣ a ∶ A

        ≣-trans : ∀ {Γ A a b c}
            → Γ ⊢ a ≣ b ∶ A
            → Γ ⊢ b ≣ c ∶ A
            ------------------------------
            → Γ ⊢ a ≣ c ∶ A

        ≣-transport₁ : ∀ {Γ 𝒾 A B a}
            → Γ ⊢ a ∶ A
            → Γ ⊢ A ≣ B ∶ 𝒾 𝒰
            ------------------------------
            → Γ ⊢ a ∶ B

        ≣-transport₂ : ∀ {Γ 𝒾 A B a b}
            → Γ ⊢ a ≣ b ∶ A
            → Γ ⊢ A ≣ B ∶ 𝒾 𝒰
            ------------------------------
            → Γ ⊢ a ≣ b ∶ B

        𝒰-CUMUL : ∀ {Γ 𝒾 A}
            → Γ ⊢ A ∶     𝒾 𝒰
            ------------------------------
            → Γ ⊢ A ∶ suc 𝒾 𝒰

            -- Γ ctx Γ⊢U :U
            -- U-INTRO
            -- Γ ⊢ A : Ui
            -- Γ⊢A:U U-CUMUL
            -- i+1
            --   i
            -- i+
            -- Γ⊢A:Ui Γ,x:A⊢B:Ui Γ,x:A⊢b≡b′ :B Π-INTRO-EQ Γ ⊢ λx.b ≡ λx.b′ : ∏(x:A)B


            -- Γ ⊢ A : Ui Γ, ∆ ⊢ b : B Wkg Γ,x:A,∆ ⊢ b : B 1
            -- Γ ⊢ A : Ui Γ, ∆ ⊢ b ≡ c : B Wkg Γ, x:A, ∆ ⊢ b ≡ c : B 2
            --   Γ, ∆[a/x] ⊢ b[a/x] ≡ c[a/x] : B[a/x] 2
    -- by-rule : ∀ {Γ J K R} → Γ ⊢ J [ R ] → Γ ⊢ K [ R ] → Γ ⊢ R J K [ R ]
Subst₁ : ∀ Γ Δ A B a b {x : Variable}
    →                   Γ ⊢ a           ∶ A
    → Δ  ++ var x ∶ A ∷ Γ ⊢ b           ∶ B
    → (Δ ++ Γ) [ a / x ]' ⊢ b [ a / x ] ∶ B [ a / x ]
Subst₁ Γ Δ A B a b {x} (in-context P) (in-context Q) = in-context (lemma start)
    where
        start : b [ a / x ] ∶ B [ a / x ] ∈ (Δ ++ var x ∶ A ∷ Γ) [ a / x ]'
        start = judgement-substitution-mono (Δ ++ var x ∶ A ∷ Γ) (_ ∶ _) a x Q

        lemma : (Δ ++ var x ∶ A ∷ Γ) [ a / x ]' ⊆ (Δ ++ Γ) [ a / x ]'
        lemma = begin
                    (Δ ++ var x ∶ A ∷ Γ) [ a / x ]'
                ≈⟨ ++-context-substitution Δ (var x ∶ A ∷ Γ) ⟩
                    Δ [ a / x ]' ++ (var x ∶ A ∷ Γ) [ a / x ]'
                ≤⟨ ++-left-mono (Δ [ a / x ]') (sbst-lemma2 Γ A a x P) ⟩
                    Δ [ a / x ]' ++ Γ [ a / x ]'
                ≈⟨ ≋-sym (++-context-substitution Δ Γ) ⟩
                    (Δ ++ Γ) [ a / x ]'
                ∎
Subst₁ Γ Δ A B a b {x} (in-context P) (Vble Q) = in-context {! judgement-substitution-mono (Δ ++ var x ∶ A ∷ Γ) (_ ∶ _) a x   !}
Subst₁ Γ Δ A B a b (in-context P) (≣-transport₁ Q Q₁) = {!   !}
Subst₁ Γ Δ A B a b (Vble Γ-ctx) Q = {!   !}
Subst₁ Γ Δ A B a b (≣-transport₁ Γ⊢a∶A Γ⊢A∶A) Q = {!   !}
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
