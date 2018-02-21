module Rule where

open import Judgement

open import Data.Empty
open import Data.List
open import Data.List.All as All
open import Data.Nat
open import Data.Product hiding (map)
open import Data.String using (String) renaming (_≟_ to _≟str_)
open import Data.Unit

open import Relation.Nullary
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to inspect[_])

open import Data.List.Any
open import Data.List.Any.Membership.Propositional

mutual

    OfHasType : Judgement → Set
    OfHasType (    a ∶ A) = ⊤
    OfHasType (a ≣ b ∶ A) = ⊥
    OfHasType (    A ∶ 𝒾 𝒰) = ⊥
    OfHasType (A ≣ B ∶ 𝒾 𝒰) = ⊥

    record IsCTX (v : Variable) (j : Judgement) : Set where
        constructor ctx
        field
            ofHasType : OfHasType j
            fresh : v FreshInJudgement j

    data CTX : List Judgement → Set where
        ctx-EMP : CTX []
        ctx-EXT : ∀ {𝒾 Γ A x}
            → (hasUniv : Γ ⊢ A ∶ 𝒾 𝒰)
            → (allCTX : All (IsCTX x) Γ)
            → CTX ((var x ∶ A) ∷ Γ)

    infix 3 _⊢_
    data _⊢_ : Context → Judgement → Set where
        Vble : ∀ {Γ 𝒾 A}
            → (isCTX : CTX Γ)
            → (A∶𝒰  : A ∶ 𝒾 𝒰 ∈ Γ)
            → (x     : Variable)
            → (x∶A   : var x ∶ A ∈ Γ)
            ------------------------------ Vble
            → Γ ⊢ var x ∶ A
-- --
-- --         -- Wkg₁ : ∀ {Γ Δ 𝒾 A B b} {x : Variable}
-- --         --     →                  Γ ⊢ A ∶ 𝒾 𝒰
-- --         --     → Δ ++             Γ ⊢ b ∶ B
-- --         --     → Δ ++ var x ∶ A ∷ Γ ⊢ b ∶ B
-- --         --
-- --         -- Subst₂ : ∀ {Γ Δ A B a b c} {x : Variable}
-- --         --     →                             Γ ⊢ a                         ∶ A
-- --         --     → Δ            ++ var x ∶ A ∷ Γ ⊢ b           ≡ c           ∶ B
-- --         --     → Δ [ a / x ]C ++             Γ ⊢ b [ a / x ] ≡ c [ a / x ] ∶ B [ a / x ]
-- --         --
-- --         -- Wkg₂ : ∀ {Γ Δ 𝒾 A B b c} {x : Variable}
-- --         --     →                  Γ ⊢     A ∶ 𝒾 𝒰
-- --         --     → Δ ++             Γ ⊢ b ≡ c ∶ B
-- --         --     → Δ ++ var x ∶ A ∷ Γ ⊢ b ≡ c ∶ B
-- --
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

        transport-∶ : ∀ {Γ 𝒾 A B a}
            → Γ ⊢ a ∶ A
            → Γ ⊢ A ≣ B ∶ 𝒾 𝒰
            ------------------------------
            → Γ ⊢ a ∶ B

        transport-≣ : ∀ {Γ 𝒾 A B a b}
            → Γ ⊢ a ≣ b ∶ A
            → Γ ⊢ A ≣ B ∶ 𝒾 𝒰
            ------------------------------
            → Γ ⊢ a ≣ b ∶ B

        𝒰-CUMUL : ∀ {Γ 𝒾 A}
            → Γ ⊢ A ∶     𝒾 𝒰
            ------------------------------
            → Γ ⊢ A ∶ suc 𝒾 𝒰
--

All-CTX-fresh : ∀ Γ Δ {x v A}
    → All (IsCTX v) (Δ ++ var x ∶ A ∷ Γ)
    → v ≢ x
All-CTX-fresh Γ [] (ctx ofHasType fresh ∷ allCTX) = proj₁ fresh
All-CTX-fresh Γ (K ∷ Δ) (px ∷ allCTX) = All-CTX-fresh Γ Δ allCTX

-- context-substitution-OfHasType : ∀ Γ J {e x} → (J ∷ Γ) [ var e / x ]C →

record ObserveContext {A : Term} {a x : Variable} (Γ Δ : Context) (a∶A : var a ∶ A ∈ Γ) : Set where
    constructor observation
    field
        v : Variable
        T : Term
        E : Context
        eq : (Δ ++ Γ) [ var a / x ]C ≡ var v ∶ T ∷ E
        -- fresh : v ≢

observe : {A : Term} {a x : Variable}
    → (Γ Δ : Context)
    → (a∶A : var a ∶ A ∈ Γ)
    → (isCTX : CTX (Δ ++ var x ∶ A ∷ Γ))
    → ObserveContext Γ Δ a∶A
observe {A} {a} {x} Γ Δ a∶A isCTX with (Δ ++ Γ) [ var a / x ]C | inspect (λ C → C [ var a / x ]C) (Δ ++ Γ)
observe {A} {a} {x} Γ Δ a∶A isCTX | [] | inspect[ eq ] = contradiction a∶A (Subst₁-empty-context Γ Δ A eq)
    where
        must-not-be-empty : ∀ Γ Δ J {a x} → (Δ ++ J ∷ Γ) [ var a / x ]C ≢ []
        must-not-be-empty []      []      J ()
        must-not-be-empty []      (_ ∷ Δ) J ()
        must-not-be-empty (_ ∷ Γ) []      J ()
        must-not-be-empty (_ ∷ Γ) (_ ∷ Δ) J ()

        Subst₁-empty-context : ∀ Γ Δ A {a x}
            → (Δ ++ Γ) [ var a / x ]C ≡ []
            → var a ∶ A ∈ Γ
            → ⊥
        Subst₁-empty-context []      Δ A empty ()
        Subst₁-empty-context (J ∷ Γ) Δ A empty a∶A = contradiction empty (must-not-be-empty Γ Δ J)
observe {A} {a} {x} Γ Δ  a∶A isCTX | var v ∶ T ∷ E | inspect[ eq ] = observation v T E eq
-- observe {A} {a} {x} Γ [] a∶A (ctx-EXT hasUniv allCTX) | var v ∶ T ∷ E | inspect[ eq ] = {! eq   !}
--     where
--         allCTX-substituted : All (IsCTX x) (var v ∶ T ∷ E)
--         allCTX-substituted = subst (All (IsCTX x)) {!   !} {!   !}
--         -- All-CTX-fresh (var v ∶ T ∷ E) []
-- observe {A} {a} {x} Γ (x₁ ∷ Δ) a∶A isCTX | var v ∶ T ∷ E | inspect[ eq ] = {!   !}
observe {A} {a} {x} Γ [] a∶A (ctx-EXT hasUniv allCTX) | _ ≣ _ ∶ _ ∷ E | inspect[ eq ]
    = contradiction eq (lemma Γ allCTX)
    where
        lemma : ∀ Γ {A E a b e x}
            → All (IsCTX x) Γ
            → Γ [ var e / x ]C ≢ a ≣ b ∶ A ∷ E
        lemma []      allCTX = λ ()
        lemma (a ∶ A ∷ Γ) allCTX = λ ()
        lemma (a ≣ b ∶ A ∷ Γ) (ctx () fresh ∷ allCTX)
        lemma (A ∶ 𝒾 𝒰 ∷ Γ) allCTX = λ ()
        lemma (A ≣ B ∶ 𝒾 𝒰 ∷ Γ) allCTX = λ ()
observe {A} {a} {x} Γ (_ ∷ Δ) a∶A (ctx-EXT {x = v} hasUniv allCTX) | _ ≣ _ ∶ _ ∷ E | inspect[ eq ] with x ≟str v
observe {A} {a} {x} Γ (_ ∷ Δ) a∶A (ctx-EXT hasUniv allCTX) | _ ≣ _ ∶ _ ∷ E | inspect[ eq ] | yes p
    = contradiction (sym p) (All-CTX-fresh Γ Δ allCTX)
observe {A} {a} {x} Γ (_ ∷ Δ) a∶A (ctx-EXT hasUniv allCTX) | _ ≣ _ ∶ _ ∷ E | inspect[ () ] | no ¬p
observe {A} {a} {x} Γ []      a∶A (ctx-EXT hasUniv allCTX) | _ ∶ _ 𝒰 ∷ E | inspect[ eq ]
    = contradiction eq (lemma Γ allCTX)
    where
        lemma : ∀ Γ {A E 𝒾 e x}
            → All (IsCTX x) Γ
            → Γ [ var e / x ]C ≢ A ∶ 𝒾 𝒰 ∷ E
        lemma []                allCTX = λ ()
        lemma (    a ∶ A   ∷ Γ) allCTX = λ ()
        lemma (a ≣ b ∶ A   ∷ Γ) allCTX = λ ()
        lemma (    A ∶ 𝒾 𝒰 ∷ Γ) (ctx () fresh ∷ allCTX)
        lemma (A ≣ B ∶ 𝒾 𝒰 ∷ Γ) allCTX = λ ()
observe {A} {a} {x} Γ (_ ∷ Δ) a∶A (ctx-EXT {x = v} hasUniv allCTX) | _ ∶ _ 𝒰 ∷ E | inspect[ eq ] with x ≟str v
observe {A} {a} {x} Γ (_ ∷ Δ) a∶A (ctx-EXT {x = v} hasUniv allCTX) | _ ∶ _ 𝒰 ∷ E | inspect[ eq ] | yes p
    = contradiction (sym p) (All-CTX-fresh Γ Δ allCTX)
observe {A} {a} {x} Γ (_ ∷ Δ) a∶A (ctx-EXT {x = v} hasUniv allCTX) | _ ∶ _ 𝒰 ∷ E | inspect[ eq ] | no ¬p
    = contradiction eq (λ ())
observe {A} {a} {x} Γ [] a∶A (ctx-EXT hasUniv allCTX) | _ ≣ _ ∶ _ 𝒰 ∷ E | inspect[ eq ]
    = contradiction eq (lemma Γ allCTX)
    where
        lemma : ∀ Γ {E 𝒾 A B e x}
            → All (IsCTX x) Γ
            → Γ [ var e / x ]C ≢ A ≣ B ∶ 𝒾 𝒰 ∷ E
        lemma []                allCTX = λ ()
        lemma (    a ∶ A   ∷ Γ) allCTX = λ ()
        lemma (a ≣ b ∶ A   ∷ Γ) allCTX = λ ()
        lemma (    A ∶ 𝒾 𝒰 ∷ Γ) allCTX = λ ()
        lemma (A ≣ B ∶ 𝒾 𝒰 ∷ Γ) (ctx () fresh ∷ allCTX)
observe {A} {a} {x} Γ (_ ∷ Δ) a∶A (ctx-EXT {x = v} hasUniv allCTX) | _ ≣ _ ∶ _ 𝒰 ∷ E | inspect[ eq ] with x ≟str v
observe {A} {a} {x} Γ (_ ∷ Δ) a∶A (ctx-EXT {x = v} hasUniv allCTX) | _ ≣ _ ∶ _ 𝒰 ∷ E | inspect[ eq ] | yes p
    = contradiction (sym p) (All-CTX-fresh Γ Δ allCTX)
observe {A} {a} {x} Γ (_ ∷ Δ) a∶A (ctx-EXT {x = v} hasUniv allCTX) | _ ≣ _ ∶ _ 𝒰 ∷ E | inspect[ eq ] | no ¬p
    = contradiction eq (λ ())

-- Subst₁-lemma-1 : ∀ Γ Δ {A B b x}
--     → (b∶B : var b ∶ B ∈ Δ ++ var x ∶ A ∷ Γ)
--     → x ≡ b
--     → Δ ≡ []
-- Subst₁-lemma-1 Γ []      b∶B eq = refl
-- Subst₁-lemma-1 Γ (K ∷ Δ) b∶B eq = {! b∶B  !}
CTX-subst-fresh : ∀ Γ {variable expr}
    → All (IsCTX variable) Γ
    → Γ [ expr / variable ]C ≡ Γ
CTX-subst-fresh []      [] = refl
CTX-subst-fresh (J ∷ Γ) (ctx ofHasType fresh ∷ allCTX)
    = cong₂ _∷_
        (J-subst-fresh fresh)
        (CTX-subst-fresh Γ allCTX)

Subst₁ : ∀ Γ Δ A B {a} {b} x
    →                   Γ ⊢ a           ∶ A             -- JA
    →  Δ ++ var x ∶ A ∷ Γ ⊢ b           ∶ B             -- JB
    → (Δ ++ Γ) [ a / x ]C ⊢ b [ a / x ] ∶ B [ a / x ]
Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) (Vble CTX-B B∶𝒰 b b∶B) with observe Γ Δ a∶A CTX-B
Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) (Vble CTX-B B∶𝒰 b b∶B) | observation v T E eq with x ≟str b
Subst₁ Γ [] A B x (Vble CTX-A A∶𝒰 a a∶A) (Vble (ctx-EXT hasUniv allCTX) B∶𝒰 b b∶B) | observation v T E eq | yes p
    = Vble isCTX univ a type
        where
            open import Function.Related
            open EquationalReasoning

            isCTX : CTX (Γ [ var a / x ]C)
            isCTX = subst CTX (PropEq.sym (CTX-subst-fresh Γ allCTX)) CTX-A

            univ : B [ var a / x ] ∶ _ 𝒰 ∈ Γ [ var a / x ]C
            univ = (
                    B ∶ _ 𝒰 ∈ var x ∶ A ∷ Γ
                ∼⟨ J-subst-mono (var x ∶ A ∷ Γ) (B ∶ _ 𝒰) ⟩
                    (B ∶ _ 𝒰) [ var a / x ]J ∈ (var x ∶ A ∷ Γ) [ var a / x ]C
                ∼⟨ C-subst-nub Γ a∶A ⟩
                    B [ var a / x ] ∶ _ 𝒰 ∈ Γ [ var a / x ]C
                ∎) B∶𝒰

            type : var a ∶ B [ var a / x ] ∈ Γ [ var a / x ]C
            type = (
                    var b ∶ B ∈ var x ∶ A ∷ Γ
                ≡⟨ cong (λ w → var w ∶ B ∈ var x ∶ A ∷ Γ) (PropEq.sym p) ⟩
                    var x ∶ B ∈ var x ∶ A ∷ Γ
                ∼⟨ J-subst-mono (var x ∶ A ∷ Γ) (var x ∶ B) ⟩
                    (var x ∶ B) [ var a / x ]J ∈ (var x ∶ A ∷ Γ) [ var a / x ]C
                ≡⟨ cong (λ w → w ∈ (var x ∶ A ∷ Γ) [ var a / x ]C) (a∶A-subst B (var a) x) ⟩
                    var a ∶ B [ var a / x ] ∈ (var x ∶ A ∷ Γ) [ var a / x ]C
                ∼⟨ C-subst-nub Γ a∶A ⟩
                    var a ∶ B [ var a / x ] ∈ Γ [ var a / x ]C
                ∎) b∶B
        -- B [ var a / x ] ∶ _ 𝒰
        --


-- C-subst-nub
    -- where
    --     ctx : Γ [ var a / x ]C
    --     ctx = ?

-- goal : Γ [ var a / x ]C ⊢ var a ∶ B [ var a / x ]
-- allCTX : All (IsCTX x) Γ

Subst₁ Γ (K ∷ Δ) A B x (Vble CTX-A A∶𝒰 a a∶A) (Vble CTX-B B∶𝒰 b b∶B) | observation v T E eq | yes p = {!   !}
-- → All (IsCTX v) (Δ ++ var x ∶ A ∷ Γ)
-- → v ≢ x


    -- subst (λ C → C ⊢ var a ∶ B [ var a / x ]) (sym eq) goal
    -- where
    --     -- (Δ ++ Γ) [ var a / x ]C ≡     var v ∶ T ∷ E
    --
    --     -- A∶𝒰 : (A ∶ .𝒾 𝒰) ∈ Γ
    --     -- B∶𝒰 : (B ∶ .𝒾 𝒰) ∈ Δ ++ var x ∶ A ∷ Γ
    --
    --     E⊢T∶𝒰 : E ⊢ T ∶ _ 𝒰
    --     E⊢T∶𝒰 = {!   !}
    --
    --     all-is-CTX : All (IsCTX v) E
    --     all-is-CTX = {!  CTX-B  !}
    --
    --     goal : var v ∶ T ∷ E ⊢ var a ∶ B [ var a / x ]
    --     goal = Vble (ctx-EXT E⊢T∶𝒰 {!   !}) {! eq  !} a {! CTX-B  !}

    -- Vble {!   !} {!   !} {!   !} {!   !}
Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) (Vble CTX-B B∶𝒰 b b∶B) | observation v T E eq | no ¬p = {!   !}
-- Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) Q with (Δ ++ Γ) [ var a / x ]C | inspect (λ C → C [ var a / x ]C) (Δ ++ Γ)
-- Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) Q | [] | inspect[ eq ] = contradiction a∶A (Subst₁-empty-context Γ Δ A eq)
-- Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) (Vble CTX-B B∶𝒰 b b∶B) | a₁ ∶ A₁ ∷ E | inspect[ eq ] = {! a∶A  !}
-- Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) (Vble CTX-B B∶𝒰 b b∶B) | a₁ ≣ b₁ ∶ A₁ ∷ E | inspect[ eq ] = {!   !}
-- Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) (Vble CTX-B B∶𝒰 b b∶B) | A₁ ∶ 𝒾 𝒰 ∷ E | inspect[ eq ] = {!   !}
-- Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) (Vble CTX-B B∶𝒰 b b∶B) | A₁ ≣ B₁ ∶ 𝒾 𝒰 ∷ E | inspect[ eq ] = {!   !}
Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) (transport-∶ Q Q₁) = {!   !}
Subst₁ Γ Δ A B x (transport-∶ P P₁) Q = {!   !}



-- Subst₁-lemma1 : ∀ Γ e x
--     → (ctx : All (CtxProp x) Γ)
--     → Γ [ var e / x ]C ≡ Γ
-- Subst₁-lemma1 [] e x []     = refl
-- Subst₁-lemma1 ((var w ∶ A)   ∷ Γ) e x (px ∷ ctx) with w ≟str x
-- Subst₁-lemma1 (var w ∶ A ∷ Γ) e x (prop ∷ ctx) | yes p = contradiction (sym p) (proj₁ prop)
-- Subst₁-lemma1 (var w ∶ A ∷ Γ) e x (prop ∷ ctx) | no ¬p =
--     ≡begin
--         var w ∶ A [ var e / x ] ∷ Γ [ var e / x ]C
--     ≡⟨ cong (λ term → var w ∶ term ∷ Γ [ var e / x ]C) (fresh-substitution (proj₂ prop)) ⟩
--         var w ∶ A ∷ Γ [ var e / x ]C
--     ≡⟨ cong (λ Δ → var w ∶ A ∷ Δ) (Subst₁-lemma1 Γ e x ctx) ⟩
--         var w ∶ A ∷ Γ
--     ≡∎
--     where
--         open PropEq.≡-Reasoning renaming (begin_ to ≡begin_; _∎ to _≡∎)
-- Subst₁-lemma1 ((a ≣ b ∶ A)   ∷ Γ) e x (() ∷ ctx)
-- Subst₁-lemma1 ((    A ∶ 𝒾 𝒰) ∷ Γ) e x (() ∷ ctx)
-- Subst₁-lemma1 ((A ≣ B ∶ 𝒾 𝒰) ∷ Γ) e x (() ∷ ctx)
--
-- Subst₁-lemma2 : ∀ B a b x
--     → b ≡ x
--     → (var b ∶ B) [ var a / x ]J ≡ var a ∶ B [ var a / x ]
-- Subst₁-lemma2 B a b x b≡x with b ≟str x
-- Subst₁-lemma2 B a b x b≡x | yes p = refl
-- Subst₁-lemma2 B a b x b≡x | no ¬p = contradiction b≡x ¬p
--
-- Subst₁-lemma3 : ∀ B a b x
--     → b ≢ x
--     → (var b ∶ B) [ var a / x ]J ≡ var b ∶ B [ var a / x ]
-- Subst₁-lemma3 B a b x b≢x with b ≟str x
-- Subst₁-lemma3 B a b x b≢x | yes p = contradiction p b≢x
-- Subst₁-lemma3 B a b x b≢x | no ¬p = refl
--
-- -- ctx-EXT : ∀ {𝒾 Γ A x}≡
-- --     → Γ ⊢ A ∶ 𝒾 𝒰
-- --     → All (CtxProp x) Γ
-- --     → CTX ((var x ∶ A) ∷ Γ)
-- -- CTX-tail : ∀ Γ A x → CTX (var x ∶ A ∷ Γ) → CTX Γ
-- -- CTX-tail []                A x (ctx-EXT A∶𝒰 prop) = ctx-EMP
-- -- CTX-tail (var v ∶ B   ∷ Γ) A x (ctx-EXT A∶𝒰 (px ∷ prop)) with x ≟str v
-- -- CTX-tail (var v ∶ B   ∷ Γ) A x (ctx-EXT A∶𝒰 (px ∷ prop)) | yes p = contradiction p (proj₁ px)
-- -- CTX-tail (var v ∶ B   ∷ Γ) A x (ctx-EXT A∶𝒰 (px ∷ prop)) | no ¬p = ctx-EXT {!    !} {!   !}
-- -- CTX-tail (a ≣ b ∶ B   ∷ Γ) A x (ctx-EXT A∶𝒰 (() ∷ prop))
-- -- CTX-tail (    B ∶ 𝒾 𝒰 ∷ Γ) A x (ctx-EXT A∶𝒰 (() ∷ prop))
-- -- CTX-tail (B ≣ C ∶ 𝒾 𝒰 ∷ Γ) A x (ctx-EXT A∶𝒰 (() ∷ prop))
--
-- Subst₁ : ∀ Γ Δ A B {a} {b} x
--     →                   Γ ⊢ a           ∶ A             -- JA
--     →  Δ ++ var x ∶ A ∷ Γ ⊢ b           ∶ B             -- JB
--     → (Δ ++ Γ) [ a / x ]C ⊢ b [ a / x ] ∶ B [ a / x ]
-- Subst₁ [] Δ A B x (Vble CTX-JA A∶𝒰 a ()) (Vble CTX-JB B∶𝒰 b b∶B)
-- Subst₁ (J ∷ Γ) [] A B x (Vble CTX-JA A∶𝒰 a a∶A) (Vble CTX-JB B∶𝒰 b b∶B) with b ≟str x
-- Subst₁ (J ∷ Γ) [] A B x (Vble CTX-JA A∶𝒰 a a∶A) (Vble (ctx-EXT _ prop) B∶𝒰 b b∶B) | yes p =
--     Vble ctx hasType a hasVar
--     where
--         lemma : (J ∷ Γ) [ var a / x ]C ≡ J ∷ Γ
--         lemma = Subst₁-lemma1 _ a x prop
--
--         ctx : CTX ((J ∷ Γ) [ var a / x ]C)
--         ctx = subst CTX (sym lemma) CTX-JA
--
--         hasType' : B [ var a / x ] ∶ _ 𝒰 ∈ (var x ∶ A ∷ J ∷ Γ) [ var a / x ]C
--         hasType' = J-subst-mono (var x ∶ A ∷ J ∷ Γ) (B ∶ _ 𝒰) (var a) x B∶𝒰
--
--         hasType : B [ var a / x ] ∶ _ 𝒰 ∈ (J ∷ Γ) [ var a / x ]C
--         hasType = C-subst-nub (J ∷ Γ) A (var a) x a∶A hasType' --
--
--         hasVar'' : (var b ∶ B) [ var a / x ]J ∈ (var x ∶ A ∷ J ∷ Γ) [ var a / x ]C
--         hasVar'' = J-subst-mono (var x ∶ A ∷ J ∷ Γ) (var b ∶ B) (var a) x b∶B
--
--         lemma2 : (var b ∶ B) [ var a / x ]J ≡ var a ∶ B [ var a / x ]
--         lemma2 = Subst₁-lemma2 B a b x p
--
--         hasVar' : var a ∶ B [ var a / x ] ∈ (var x ∶ A ∷ J ∷ Γ) [ var a / x ]C
--         hasVar' = subst (λ w → w ∈ (var x ∶ A ∷ J ∷ Γ) [ var a / x ]C) lemma2 hasVar''
--         -- hasVar' : var a ∶ B [ var a / x ] ∈ (var x ∶ A ∷ J ∷ Γ) [ var a / x ]C
--         -- hasVar' = J-subst-mono (var x ∶ A ∷ J ∷ Γ) {! var a ∶ B  !} (var a) x b∶B'
--         -- b ≡ x that's why we have 'var a ∶ ...'
--         hasVar : var a ∶ B [ var a / x ] ∈ (J ∷ Γ) [ var a / x ]C
--         hasVar = C-subst-nub (J ∷ Γ) A (var a) x a∶A hasVar'
--
-- Subst₁ (J ∷ Γ) [] A B x (Vble CTX-JA A∶𝒰 a a∶A) (Vble (ctx-EXT _ prop) B∶𝒰 b b∶B) | no ¬p =
--     Vble ctx hasType b hasVar
--     where
--         lemma : (J ∷ Γ) [ var a / x ]C ≡ J ∷ Γ
--         lemma = Subst₁-lemma1 _ a x prop
--
--         ctx : CTX ((J ∷ Γ) [ var a / x ]C)
--         ctx = subst CTX (sym lemma) CTX-JA
--
--         hasType' : B [ var a / x ] ∶ _ 𝒰 ∈ (var x ∶ A ∷ J ∷ Γ) [ var a / x ]C
--         hasType' = J-subst-mono (var x ∶ A ∷ J ∷ Γ) (B ∶ _ 𝒰) (var a) x B∶𝒰
--
--         hasType : B [ var a / x ] ∶ _ 𝒰 ∈ (J ∷ Γ) [ var a / x ]C
--         hasType = C-subst-nub (J ∷ Γ) A (var a) x a∶A hasType'
--
--         hasVar'' : (var b ∶ B) [ var a / x ]J ∈ (var x ∶ A ∷ J ∷ Γ) [ var a / x ]C
--         hasVar'' = J-subst-mono (var x ∶ A ∷ J ∷ Γ) (var b ∶ B) (var a) x b∶B
--         --
--         lemma2 : (var b ∶ B) [ var a / x ]J ≡ var b ∶ B [ var a / x ]
--         lemma2 = Subst₁-lemma3 B a b x ¬p
--
--         hasVar' : var b ∶ B [ var a / x ] ∈ (var x ∶ A ∷ J ∷ Γ) [ var a / x ]C
--         hasVar' = subst (λ w → w ∈ (var x ∶ A ∷ J ∷ Γ) [ var a / x ]C) lemma2 hasVar''
--
--         hasVar : var b ∶ B [ var a / x ] ∈ (J ∷ Γ) [ var a / x ]C
--         hasVar = C-subst-nub (J ∷ Γ) A (var a) x a∶A hasVar' -- C-subst-nub (J ∷ Γ) A (var a) x a∶A hasVar'
--
-- Subst₁ (J ∷ Γ) (K ∷ Δ) A B x (Vble CTX-JA A∶𝒰 a a∶A) (Vble CTX-JB B∶𝒰 b b∶B) with (K ∷ Δ ++ J ∷ Γ) [ var a / x ]C | inspect (λ w → (K ∷ Δ ++ J ∷ Γ) [ var a / w ]C) x
-- Subst₁ (J ∷ Γ) (K ∷ Δ) A B x (Vble CTX-JA A∶𝒰 a a∶A) (Vble CTX-JB B∶𝒰 b b∶B) | [] | inspect[ () ]
-- Subst₁ (J ∷ Γ) (K ∷ Δ) A B x (Vble CTX-JA A∶𝒰 a a∶A) (Vble CTX-JB B∶𝒰 b b∶B) | L ∷ E | inspect[ eq ] with b ≟str x
-- Subst₁ (J ∷ Γ) (K ∷ Δ) A B x (Vble CTX-JA A∶𝒰 a a∶A) (Vble CTX-JB B∶𝒰 b b∶B) | L ∷ E | inspect[ eq ] | yes p =
--     Vble ctx {!   !} {!   !} {!   !}
--     where
--
--         ctx : CTX (L ∷ E)
--         ctx = {! ctx-EXT  !}
--
-- Subst₁ (J ∷ Γ) (K ∷ Δ) A B x (Vble CTX-JA A∶𝒰 a a∶A) (Vble CTX-JB B∶𝒰 b b∶B) | L ∷ E | inspect[ eq ] | no ¬p = {!   !}
--     -- {! Vble  !}
-- Subst₁ Γ Δ A B x (Vble CTX-Γ U v ∈Γ) (transport-∶ Q Q₁) = {!   !}
-- Subst₁ Γ Δ A B x (transport-∶ P P₁) Q = {!   !}
-- -- Subst₁ Γ Δ A B .(var _) b x (Vble P Q R) (≣-transport₁ S T) = {!   !}
-- -- Subst₁ Γ Δ A B a b x (≣-transport₁ P Q) S = {!   !}
-- --
-- -- -- Subst₁ Γ Δ A B a b {x} (in-context P) (in-context Q) = in-context (lemma start)
-- -- --     where
-- -- --         start : b [ a / x ] ∶ B [ a / x ] ∈ (Δ ++ var x ∶ A ∷ Γ) [ a / x ]C
-- -- --         start = J-subst-mono (Δ ++ var x ∶ A ∷ Γ) (_ ∶ _) a x Q
-- -- --
-- -- --         lemma : (Δ ++ var x ∶ A ∷ Γ) [ a / x ]C ⊆ (Δ ++ Γ) [ a / x ]C
-- -- --         lemma = begin
-- -- --                     (Δ ++ var x ∶ A ∷ Γ) [ a / x ]C
-- -- --                 ≈⟨ ++-context-substitution Δ (var x ∶ A ∷ Γ) ⟩
-- -- --                     Δ [ a / x ]C ++ (var x ∶ A ∷ Γ) [ a / x ]C
-- -- --                 ≤⟨ ++-left-mono (Δ [ a / x ]C) (sbst-lemma2 Γ A a x P) ⟩
-- -- --                     Δ [ a / x ]C ++ Γ [ a / x ]C
-- -- --                 ≈⟨ ≋-sym (++-context-substitution Δ Γ) ⟩
-- -- --                     (Δ ++ Γ) [ a / x ]C
-- -- --                 ∎
-- -- -- Subst₁ Γ Δ A B a b {x} (in-context P) (Vble Q) = in-context {! J-subst-mono (Δ ++ var x ∶ A ∷ Γ) (_ ∶ _) a x   !}
-- -- -- Subst₁ Γ Δ A B a b (in-context P) (≣-transport₁ Q Q₁) = {!   !}
-- -- -- Subst₁ Γ Δ A B a b (Vble Γ-ctx) Q = {!   !}
-- -- -- Subst₁ Γ Δ A B a b (≣-transport₁ Γ⊢a∶A Γ⊢A∶A) Q = {!   !}
-- -- -- infix 3 _⊢_
-- -- -- _⊢_ : Context → Judgement → Set
-- -- -- Γ ⊢ J = J ∈ Γ
-- -- --
-- -- -- data CTX : Context → Set where
-- -- --     ctx-EMP : CTX []
-- -- --     ctx-EXT : ∀ {Γ A 𝒰 x} → Γ ⊢ A ∶ 𝒰 → CTX ((x ∶ A) ∷ Γ)
-- --
-- -- -- data Structural : Set where
-- -- --     Vble : ∀ {Γ x A} → CTX Γ → Γ ⊢ x ∶ A → Structural
-- -- --     subst₁ : ∀ {Γ Δ a b x A B} → Γ ⊢ a ∶ A
