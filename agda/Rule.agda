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

-- ???
-- CTX-wellformed : ∀ Γ a A → Γ ⊢ a ∶ A → CTX Γ
-- CTX-wellformed []      a A P = ctx-EMP
-- CTX-wellformed (J ∷ Γ) .(var x) A (Vble isCTX A∶𝒰 x x∶A) = isCTX
-- CTX-wellformed (J ∷ Γ) a A (transport-∶ P ())

CTX-fresh : ∀ Γ Δ {x v A}
    → All (IsCTX v) (Δ ++ var x ∶ A ∷ Γ)
    → v ≢ x
CTX-fresh Γ [] (ctx ofHasType fresh ∷ allCTX) = proj₁ fresh
CTX-fresh Γ (K ∷ Δ) (px ∷ allCTX) = CTX-fresh Γ Δ allCTX

CTX-subst-fresh : ∀ Γ {variable expr}
    → All (IsCTX variable) Γ
    → Γ [ expr / variable ]C ≡ Γ
CTX-subst-fresh []      [] = refl
CTX-subst-fresh (J ∷ Γ) (ctx ofHasType fresh ∷ allCTX)
    = cong₂ _∷_
        (J-subst-fresh fresh)
        (CTX-subst-fresh Γ allCTX)

-- -- All (IsCTX k) (Δ ++ var x ∶ A ∷ Γ)
-- CTX-subst : ∀ Γ a variable {A expr}
--     → a ≢ variable
--     → CTX ((var a ∶ A ∷ Γ) [ expr / variable ]C) ≡ CTX (var a ∶ A ∷ Γ)
-- CTX-subst Γ a variable P with variable ≟str a
-- CTX-subst Γ a variable P | yes p = contradiction (sym p) P
-- CTX-subst Γ a variable P | no ¬p = cong CTX {!   !}

record ObserveContext {A : Term} {a : Variable} (Γ Δ : Context) (x : Variable) (a∶A : var a ∶ A ∈ Γ) : Set where
    constructor observation
    field
        v : Variable
        T : Term
        E : Context
        eq : (Δ ++ Γ) [ var a / x ]C ≡ var v ∶ T ∷ E
        -- isCTX : CTX (var v ∶ T ∷ E)
        -- fresh : v ≢

observe : {A : Term} {a x : Variable}
    → (Γ Δ : Context)
    → (a∶A : var a ∶ A ∈ Γ)
    → (isCTX : CTX (Δ ++ var x ∶ A ∷ Γ))
    → ObserveContext Γ Δ x a∶A
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
observe {A} {a} {x} [] [] a∶A (ctx-EXT hasUniv allCTX) | var v ∶ T ∷ E | inspect[ () ]
observe {A} {a} {x} (J ∷ Γ) [] a∶A (ctx-EXT hasUniv allCTX) | var v ∶ T ∷ E | inspect[ eq ] = observation v T E eq
observe {A} {a} {x} Γ (K ∷ Δ) a∶A isCTX | var v ∶ T ∷ E | inspect[ eq ] = observation v T E eq
--  observation v T E eq {! isCTX  !}
-- observe {A} {a} {x} Γ [] a∶A (ctx-EXT hasUniv allCTX) | var v ∶ T ∷ E | inspect[ eq ] = {! eq   !}
--     where
--         allCTX-substituted : All (IsCTX x) (var v ∶ T ∷ E)
--         allCTX-substituted = subst (All (IsCTX x)) {!   !} {!   !}
--         -- CTX-fresh (var v ∶ T ∷ E) []
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
    = contradiction (sym p) (CTX-fresh Γ Δ allCTX)
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
    = contradiction (sym p) (CTX-fresh Γ Δ allCTX)
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
    = contradiction (sym p) (CTX-fresh Γ Δ allCTX)
observe {A} {a} {x} Γ (_ ∷ Δ) a∶A (ctx-EXT {x = v} hasUniv allCTX) | _ ≣ _ ∶ _ 𝒰 ∷ E | inspect[ eq ] | no ¬p
    = contradiction eq (λ ())

isCTX-lemma : ∀ Γ Δ A a x
    → CTX Γ
    → CTX (Δ ++ var x ∶ A ∷ Γ)
    → var a ∶ A ∈ Γ
    → CTX ((Δ ++ Γ) [ var a / x ]C)
isCTX-lemma Γ [] A a x CTX-A (ctx-EXT hasUniv allCTX) a∶A
    = subst CTX (PropEq.sym (CTX-subst-fresh Γ allCTX)) CTX-A
isCTX-lemma Γ (var k ∶ K ∷ Δ) A a x CTX-A (ctx-EXT hasUniv allCTX) a∶A with x ≟str k
isCTX-lemma Γ (var k ∶ K ∷ Δ) A a x CTX-A (ctx-EXT hasUniv allCTX) a∶A | yes p
    = contradiction (sym p) (CTX-fresh Γ Δ allCTX)
isCTX-lemma Γ (var k ∶ K ∷ Δ) A a x CTX-A (ctx-EXT hasUniv allCTX) a∶A | no ¬p
    = ctx-EXT univ type
    where
        open import Function.Related
        open EquationalReasoning

        univ : (Δ ++ Γ) [ var a / x ]C ⊢ K [ var a / x ] ∶ _ 𝒰
        univ = (
                Δ ++ (var x ∶ A) ∷ Γ ⊢ K ∶ _ 𝒰
            ∼⟨ {!   !} ⟩
                {! a∶A  !}
            ∼⟨ {!   !} ⟩
                {!   !}
            ∼⟨ {!   !} ⟩
                {!   !}
            ∼⟨ {!   !} ⟩
                ((Δ ++ Γ) [ var a / x ]C ⊢ K [ var a / x ] ∶ _ 𝒰)
            ∎) hasUniv
        type : All (IsCTX k) ((Δ ++ Γ) [ var a / x ]C)
        type = {! allCTX  !}

        -- (Δ ++ var x ∶ A ∷ Γ) ≡ ((Δ ++ Γ) [ var a / x ]C)

-- isCTX-lemma Γ (var k ∶ K ∷ []) A a x CTX-A (ctx-EXT hasUniv (ctx ofHasType fresh ∷ allCTX)) a∶A | no ¬p
--     = ctx-EXT univ type
--     where
--         open import Function.Related
--         open EquationalReasoning
--
--         univ : Γ [ var a / x ]C ⊢ K [ var a / x ] ∶ _ 𝒰
--         univ = (
--                 (var x ∶ A) ∷ Γ ⊢ K ∶ _ 𝒰
--             ∼⟨ {!   !} ⟩
--                 {! a∶A  !}
--             ∼⟨ {!   !} ⟩
--                 {!   !}
--             ∼⟨ {!   !} ⟩
--                 {!   !}
--             ∼⟨ {!   !} ⟩
--                 (Γ [ var a / x ]C ⊢ K [ var a / x ] ∶ _ 𝒰)
--             ∎) hasUniv
--         type : All (IsCTX k) (Γ [ var a / x ]C)
--         type = {! allCTX  !}
--     -- CTX-subst-fresh
-- isCTX-lemma Γ (var k ∶ K ∷ L ∷ Δ) A a x CTX-A (ctx-EXT hasUniv (ctx ofHasType fresh ∷ allCTX)) a∶A | no ¬p
--     = ctx-EXT {!   !} {!   !}
    -- = subst CTX eq (ctx-EXT hasUniv allCTX)
    -- -- -- allCTX : All (IsCTX k) (Δ ++ var x ∶ A ∷ Γ)
    -- --
    -- --
    -- where
    --     eq : var k ∶ K ∷ Δ ++ var x ∶ A ∷ Γ ≡ (var k ∶ K [ var a / x ]) ∷ (Δ ++ Γ) [ var a / x ]C
    --     eq = {!   !}

Subst₁ : ∀ Γ Δ A B {a} {b} x
    →                   Γ ⊢ a           ∶ A             -- JA
    →  Δ ++ var x ∶ A ∷ Γ ⊢ b           ∶ B             -- JB
    → (Δ ++ Γ) [ a / x ]C ⊢ b [ a / x ] ∶ B [ a / x ]
Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) (Vble CTX-B B∶𝒰 b b∶B) with observe Γ Δ a∶A CTX-B
Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) (Vble CTX-B B∶𝒰 b b∶B) | observation v T E eq with x ≟str b
Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) (Vble CTX-B B∶𝒰 b b∶B) | observation v T E eq | yes p
    = Vble isCTX univ a type
    where
        open import Function.Related
        open EquationalReasoning

        -- eq : (Δ ++ Γ) [ var a / x ]C ≡ var v ∶ T ∷ E
        -- eq = ?

        cc : {!   !}
        cc = {!   !}

        isCTX : CTX ((Δ ++ Γ) [ var a / x ]C)
        isCTX = isCTX-lemma Γ Δ A a x CTX-A CTX-B a∶A

        univ : B [ var a / x ] ∶ _ 𝒰 ∈ (Δ ++ Γ) [ var a / x ]C
        univ = (
                B ∶ _ 𝒰 ∈ Δ ++ var x ∶ A ∷ Γ
            ∼⟨ J-subst-mono (Δ ++ var x ∶ A ∷ Γ) (B ∶ _ 𝒰) ⟩
                B [ var a / x ] ∶ _ 𝒰 ∈  (Δ ++ var x ∶ A ∷ Γ) [ var a / x ]C
            ∼⟨ C-subst-nub Γ Δ a∶A ⟩
                B [ var a / x ] ∶ _ 𝒰 ∈ (Δ ++ Γ) [ var a / x ]C
            ∎) B∶𝒰

        type : var a ∶ B [ var a / x ] ∈ (Δ ++ Γ) [ var a / x ]C
        type = (
                var b ∶ B ∈ Δ ++ var x ∶ A ∷ Γ
            ≡⟨ cong (λ w → var w ∶ B ∈ Δ ++ var x ∶ A ∷ Γ) (PropEq.sym p) ⟩
                var x ∶ B ∈ Δ ++ var x ∶ A ∷ Γ
            ∼⟨ J-subst-mono (Δ ++ var x ∶ A ∷ Γ) (var x ∶ B) ⟩
                (var x ∶ B) [ var a / x ]J ∈ (Δ ++ var x ∶ A ∷ Γ) [ var a / x ]C
            ≡⟨ cong (λ w → w ∈ (Δ ++ var x ∶ A ∷ Γ) [ var a / x ]C) (a∶A-subst B (var a) x) ⟩
                var a ∶ B [ var a / x ] ∈ (Δ ++ var x ∶ A ∷ Γ) [ var a / x ]C
            ∼⟨ C-subst-nub Γ Δ a∶A ⟩
                var a ∶ B [ var a / x ] ∈ (Δ ++ Γ) [ var a / x ]C
            ∎) b∶B
Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) (Vble CTX-B B∶𝒰 b b∶B) | observation v T E eq | no ¬p
    = Vble isCTX univ b type
    where
        open import Function.Related
        open EquationalReasoning

        isCTX : CTX ((Δ ++ Γ) [ var a / x ]C)
        isCTX = isCTX-lemma Γ Δ A a x CTX-A CTX-B a∶A

        univ : B [ var a / x ] ∶ _ 𝒰 ∈ (Δ ++ Γ) [ var a / x ]C
        univ = (
                B ∶ _ 𝒰 ∈ Δ ++ var x ∶ A ∷ Γ
            ∼⟨ J-subst-mono (Δ ++ var x ∶ A ∷ Γ) (B ∶ _ 𝒰) ⟩
                B [ var a / x ] ∶ _ 𝒰 ∈  (Δ ++ var x ∶ A ∷ Γ) [ var a / x ]C
            ∼⟨ C-subst-nub Γ Δ a∶A ⟩
                B [ var a / x ] ∶ _ 𝒰 ∈ (Δ ++ Γ) [ var a / x ]C
            ∎) B∶𝒰

        type : var b ∶ B [ var a / x ] ∈ (Δ ++ Γ) [ var a / x ]C
        type = (
                var b ∶ B ∈ Δ ++ var x ∶ A ∷ Γ
            ∼⟨ J-subst-mono (Δ ++ var x ∶ A ∷ Γ) (var b ∶ B) ⟩
                var b [ var a / x ] ∶ B [ var a / x ] ∈ (Δ ++ var x ∶ A ∷ Γ) [ var a / x ]C
            ≡⟨ cong (λ w → w ∶ B [ var a / x ] ∈ (Δ ++ var x ∶ A ∷ Γ) [ var a / x ]C) (subst-fresh ¬p) ⟩
                var b ∶ B [ var a / x ] ∈ (Δ ++ var x ∶ A ∷ Γ) [ var a / x ]C
            ∼⟨ C-subst-nub Γ Δ a∶A ⟩
                var b ∶ B [ var a / x ] ∈ (Δ ++ Γ) [ var a / x ]C
            ∎) b∶B
-- Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) Q with (Δ ++ Γ) [ var a / x ]C | inspect (λ C → C [ var a / x ]C) (Δ ++ Γ)
-- Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) Q | [] | inspect[ eq ] = contradiction a∶A (Subst₁-empty-context Γ Δ A eq)
-- Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) (Vble CTX-B B∶𝒰 b b∶B) | a₁ ∶ A₁ ∷ E | inspect[ eq ] = {! a∶A  !}
-- Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) (Vble CTX-B B∶𝒰 b b∶B) | a₁ ≣ b₁ ∶ A₁ ∷ E | inspect[ eq ] = {!   !}
-- Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) (Vble CTX-B B∶𝒰 b b∶B) | A₁ ∶ 𝒾 𝒰 ∷ E | inspect[ eq ] = {!   !}
-- Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) (Vble CTX-B B∶𝒰 b b∶B) | A₁ ≣ B₁ ∶ 𝒾 𝒰 ∷ E | inspect[ eq ] = {!   !}
Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) (transport-∶ Q Q₁) = {!   !}
Subst₁ Γ Δ A B x (transport-∶ P P₁) Q = {!   !}
