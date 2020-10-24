module Rule where

open import Judgement

open import Data.Empty
open import Data.List
open import Data.List.All as All hiding (map)
open import Data.Nat
open import Data.Product hiding (map)
open import Data.String using (String) renaming (_≟_ to _≟str_)
open import Data.Unit

open import Relation.Nullary
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to inspect[_])

open import Data.List.Any as Any hiding (map)
open import Data.List.Any.Membership.Propositional

mutual
    data CTX : List Judgement → Set where
        ctx-EMP : CTX []
        ctx-EXT : ∀ {𝒾 Γ A x}
            → (A∶𝒰 : Γ ⊢ A ∶ 𝒾 𝒰)
            → (x#A : x # A)
            → (x∶A#Γ : var x ∶ A ♯C Γ)
            → (CTX-Γ : CTX Γ)
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

CTX-fresh : ∀ Γ Δ {x variable A}
    → variable #C (Δ ++ var x ∶ A ∷ Γ)
    → variable ≢ x
CTX-fresh Γ []      (fresh ∷ restFresh) = proj₁ fresh
CTX-fresh Γ (K ∷ Δ) (fresh ∷ restFresh) = CTX-fresh Γ Δ restFresh

CTX-subst-fresh : ∀ Γ {variable expr}
    → variable #C Γ
    → Γ [ expr / variable ]C ≡ Γ
CTX-subst-fresh []      [] = refl
CTX-subst-fresh (J ∷ Γ) (fresh ∷ restFresh)
    = cong₂ _∷_
        (J-subst-fresh fresh)
        (CTX-subst-fresh Γ restFresh)


-- record ObserveContext {A : Term} {a : Variable} (Γ Δ : Context) (x : Variable) (a∶A : var a ∶ A ∈ Γ) : Set where
--     constructor observation
--     field
--         v : Variable
--         T : Term
--         E : Context
--         eq : (Δ ++ Γ) [ var a / x ]C ≡ var v ∶ T ∷ E
--
-- observe : {A : Term} {a x : Variable}
--     → (Γ Δ : Context)
--     → (a∶A : var a ∶ A ∈ Γ)
--     → (isCTX : CTX (Δ ++ var x ∶ A ∷ Γ))
--     → ObserveContext Γ Δ x a∶A
-- observe {A} {a} {x} Γ Δ a∶A isCTX with (Δ ++ Γ) [ var a / x ]C | inspect (λ C → C [ var a / x ]C) (Δ ++ Γ)
-- observe {A} {a} {x} Γ Δ a∶A isCTX | [] | inspect[ eq ] = contradiction a∶A (Subst₁-empty-context Γ Δ A eq)
--     where
--         must-not-be-empty : ∀ Γ Δ J {a x} → (Δ ++ J ∷ Γ) [ var a / x ]C ≢ []
--         must-not-be-empty []      []      J ()
--         must-not-be-empty []      (_ ∷ Δ) J ()
--         must-not-be-empty (_ ∷ Γ) []      J ()
--         must-not-be-empty (_ ∷ Γ) (_ ∷ Δ) J ()
--
--         Subst₁-empty-context : ∀ Γ Δ A {a x}
--             → (Δ ++ Γ) [ var a / x ]C ≡ []
--             → var a ∶ A ∈ Γ
--             → ⊥
--         Subst₁-empty-context []      Δ A empty ()
--         Subst₁-empty-context (J ∷ Γ) Δ A empty a∶A = contradiction empty (must-not-be-empty Γ Δ J)
-- observe {A} {a} {x} [] [] a∶A isCTX | var v ∶ T ∷ E | inspect[ () ]
-- observe {A} {a} {x} (J ∷ Γ) [] a∶A isCTX | var v ∶ T ∷ E | inspect[ eq ] = observation v T E eq
-- observe {A} {a} {x} Γ (K ∷ Δ) a∶A isCTX | var v ∶ T ∷ E | inspect[ eq ] = observation v T E eq
-- --  observation v T E eq {! isCTX  !}
-- -- observe {A} {a} {x} Γ [] a∶A (ctx-EXT hasUniv allCTX) | var v ∶ T ∷ E | inspect[ eq ] = {! eq   !}
-- --     where
-- --         allCTX-substituted : All (IsCTX x) (var v ∶ T ∷ E)
-- --         allCTX-substituted = subst (All (IsCTX x)) {!   !} {!   !}
-- --         -- CTX-fresh (var v ∶ T ∷ E) []
-- -- observe {A} {a} {x} Γ (x₁ ∷ Δ) a∶A isCTX | var v ∶ T ∷ E | inspect[ eq ] = {!   !}
-- observe {A} {a} {x} Γ [] a∶A (ctx-EXT hasUniv freshInType allFresh allOfHasType) | _ ≣ _ ∶ _ ∷ E | inspect[ eq ]
--     = contradiction eq (lemma Γ allOfHasType)
--     where
--         lemma : ∀ Γ {A E a b e x}
--             → All OfHasType Γ
--             → Γ [ var e / x ]C ≢ a ≣ b ∶ A ∷ E
--         lemma []                allOfHasType = λ ()
--         lemma (a     ∶   A ∷ Γ) allOfHasType = λ ()
--         lemma (a ≣ b ∶ A ∷ Γ)   (() ∷ allOfHasType)
--         lemma (A     ∶ 𝒾 𝒰 ∷ Γ) allOfHasType = λ ()
--         lemma (A ≣ B ∶ 𝒾 𝒰 ∷ Γ) allOfHasType = λ ()
-- observe {A} {a} {x} Γ (_ ∷ Δ) a∶A (ctx-EXT {x = v} hasUniv freshInType allFresh allOfHasType) | _ ≣ _ ∶ _ ∷ E | inspect[ eq ] with x ≟str v
-- observe {A} {a} {x} Γ (_ ∷ Δ) a∶A (ctx-EXT hasUniv freshInType (fresh ∷ allFresh) allOfHasType) | _ ≣ _ ∶ _ ∷ E | inspect[ eq ] | yes p
--     = ?
--     -- = contradiction (sym p) (CTX-fresh Γ Δ ?)
-- observe {A} {a} {x} Γ (_ ∷ Δ) a∶A (ctx-EXT hasUniv freshInType allFresh allOfHasType) | _ ≣ _ ∶ _ ∷ E | inspect[ () ] | no ¬p
-- observe {A} {a} {x} Γ []      a∶A (ctx-EXT hasUniv freshInType allFresh allOfHasType) | _ ∶ _ 𝒰 ∷ E | inspect[ eq ]
--     = contradiction eq (lemma Γ allOfHasType)
--     where
--         lemma : ∀ Γ {A E 𝒾 e x}
--             → All OfHasType Γ
--             → Γ [ var e / x ]C ≢ A ∶ 𝒾 𝒰 ∷ E
--         lemma []                allOfHasType = λ ()
--         lemma (    a ∶ A   ∷ Γ) allOfHasType = λ ()
--         lemma (a ≣ b ∶ A   ∷ Γ) allOfHasType = λ ()
--         lemma (    A ∶ 𝒾 𝒰 ∷ Γ) (() ∷ allOfHasType)
--         lemma (A ≣ B ∶ 𝒾 𝒰 ∷ Γ) allOfHasType = λ ()
-- observe {A} {a} {x} Γ (_ ∷ Δ) a∶A (ctx-EXT {x = v} hasUniv allFresh allOfHasType) | _ ∶ _ 𝒰 ∷ E | inspect[ eq ] with x ≟str v
-- observe {A} {a} {x} Γ (_ ∷ Δ) a∶A (ctx-EXT {x = v} hasUniv (fresh ∷ allFresh) allOfHasType) | _ ∶ _ 𝒰 ∷ E | inspect[ eq ] | yes p
--     = contradiction (sym p) (CTX-fresh Γ Δ allFresh)
-- observe {A} {a} {x} Γ (_ ∷ Δ) a∶A (ctx-EXT {x = v} hasUniv allFresh allOfHasType) | _ ∶ _ 𝒰 ∷ E | inspect[ eq ] | no ¬p
--     = contradiction eq (λ ())
-- observe {A} {a} {x} Γ [] a∶A (ctx-EXT hasUniv freshInType allFresh allOfHasType) | _ ≣ _ ∶ _ 𝒰 ∷ E | inspect[ eq ]
--     = contradiction eq (lemma Γ allOfHasType)
--     where
--         lemma : ∀ Γ {E 𝒾 A B e x}
--             → All OfHasType Γ
--             → Γ [ var e / x ]C ≢ A ≣ B ∶ 𝒾 𝒰 ∷ E
--         lemma []                allOfHasType = λ ()
--         lemma (    a ∶ A   ∷ Γ) allOfHasType = λ ()
--         lemma (a ≣ b ∶ A   ∷ Γ) allOfHasType = λ ()
--         lemma (    A ∶ 𝒾 𝒰 ∷ Γ) allOfHasType = λ ()
--         lemma (A ≣ B ∶ 𝒾 𝒰 ∷ Γ) (() ∷ allOfHasType)
-- observe {A} {a} {x} Γ (_ ∷ Δ) a∶A (ctx-EXT {x = v} hasUniv freshInType allFresh allOfHasType) | _ ≣ _ ∶ _ 𝒰 ∷ E | inspect[ eq ] with x ≟str v
-- observe {A} {a} {x} Γ (_ ∷ Δ) a∶A (ctx-EXT {x = v} hasUniv freshInType (fresh ∷ allFresh) allOfHasType) | _ ≣ _ ∶ _ 𝒰 ∷ E | inspect[ eq ] | yes p
--     = contradiction (sym p) (CTX-fresh Γ Δ allFresh)
-- observe {A} {a} {x} Γ (_ ∷ Δ) a∶A (ctx-EXT {x = v} hasUniv freshInType allFresh allOfHasType) | _ ≣ _ ∶ _ 𝒰 ∷ E | inspect[ eq ] | no ¬p
--     = contradiction eq (λ ())

    -- -- Subst₁ : ∀ Γ Δ A B {a} {b} x
    -- --     →                   Γ ⊢ a           ∶ A             -- JA
    -- --     →  Δ ++ var x ∶ A ∷ Γ ⊢ b           ∶ B             -- JB
    -- --     → (Δ ++ Γ) [ a / x ]C ⊢ b [ a / x ] ∶ B [ a / x ]


Univ-Wkg₁ : ∀ {𝒾} Γ Δ {A B : Term} {x : Variable}
    → Δ ++ Γ ⊢ B ∶ 𝒾 𝒰
    → (Δ ++ var x ∶ A ∷ Γ) ⊢ B ∶ 𝒾 𝒰
Univ-Wkg₁ {zero} Γ Δ ()
Univ-Wkg₁ {suc 𝒾} Γ Δ (𝒰-CUMUL B∶𝒰) = 𝒰-CUMUL (Univ-Wkg₁ Γ Δ B∶𝒰)

-- Weakening Lemmata
module Weakening where

    ♯C-weakening : ∀ Γ Δ {A x V v}
        → var v ∶ V ♯C (Δ ++ Γ)
        → var v ∶ V ♯C (Δ ++ var x ∶ A ∷ Γ)
    ♯C-weakening Γ []       P = {!   !} ∷ P
    ♯C-weakening Γ (K ∷ Δ)  (v#K ∷ P) = {!   !}

    CTX-Wkg₁ : ∀ {𝒾} Γ Δ A x
        → Γ ⊢ A ∶ 𝒾 𝒰
        → x # A
        → var x ∶ A ♯C (Δ ++ Γ)
        → CTX (Δ ++ Γ)
        → CTX (Δ ++ var x ∶ A ∷ Γ)
    CTX-Wkg₁ Γ [] A x A∶𝒰 x#A x∶A#Γ isCTX
        = ctx-EXT A∶𝒰 x#A x∶A#Γ isCTX
    CTX-Wkg₁ Γ (.(var _ ∶ _) ∷ Δ) A x A∶𝒰 x#A (ps ∷ x∶A#Γ) (ctx-EXT V∶𝒰 v#V v∶V#Γ isCTX)
        = ctx-EXT (Univ-Wkg₁ Γ Δ V∶𝒰) v#V (♯C-weakening Γ Δ {! ps  !})
            (CTX-Wkg₁ Γ Δ A x A∶𝒰 x#A x∶A#Γ isCTX)
    -- CTX-Wkg₁ Γ (.(var _ ∶ _) ∷ Δ) A x A∶𝒰 x∶A#Γ (ctx-EXT V∶𝒰 v#V v#Γ isCTX)
    --     = ctx-EXT (Univ-Wkg₁ Γ Δ V∶𝒰) v#V (#C-weakening Γ Δ {!   !} v#Γ) (CTX-Wkg₁ Γ Δ A x A∶𝒰 x#A x#Γ isCTX)


Wkg₁ : ∀ {𝒾} Γ Δ A B {b} x
    → x # A
    → var x ∶ A ♯C (Δ ++ Γ)
    → Γ ⊢ A ∶ 𝒾 𝒰
    → Δ ++ Γ ⊢ b ∶ B
    → Δ ++ var x ∶ A ∷ Γ ⊢ b ∶ B
Wkg₁ Γ Δ A B x x#A x∶A#Γ A∶𝒰 (Vble isCTX B∶𝒰 b b∶B)
    = Vble ctx univ _ type
    where
        ctx : CTX (Δ ++ var x ∶ A ∷ Γ)
        ctx = Weakening.CTX-Wkg₁ Γ Δ A x A∶𝒰 x#A x∶A#Γ isCTX

        univ : B ∶ _ 𝒰 ∈ Δ ++ var x ∶ A ∷ Γ
        univ = weakening Δ Γ (var x ∶ A) B∶𝒰

        type : var b ∶ B ∈ Δ ++ var x ∶ A ∷ Γ
        type = weakening Δ Γ (var x ∶ A) b∶B

Wkg₁ Γ Δ A B x x#A x#Γ A∶𝒰 (transport-∶ Q ())
-- Wkg₁ [] [] A B .(var x₁) x x-fresh x-allFresh P (Vble isCTX A∶𝒰 x₁ x∶A)
--     = Vble ctx univ x₁ type
--     where
--         ctx : CTX (var x ∶ A ∷ [])
--         ctx = ctx-EXT P x-fresh [] []
--
--         univ : B ∶ _ 𝒰 ∈ var x ∶ A ∷ []
--         univ = there A∶𝒰
--
--         type : var x₁ ∶ B ∈ var x ∶ A ∷ []
--         type = there x∶A
--
-- Wkg₁ [] [] A B b x x-fresh x-allFresh P (transport-∶ Q ())
-- Wkg₁ (.(var _ ∶ _) ∷ Γ) [] A B .(var x₁) x x-fresh x-allFresh P
--     (Vble (ctx-EXT hasUniv freshInType allFresh allOfHasType) A∶𝒰 x₁ x∶A)
--     = Vble ctx univ x₁ type
--     where
--         ctx : CTX (var x ∶ A ∷ _ ∷ Γ)
--         ctx = ctx-EXT P x-fresh x-allFresh (tt ∷ allOfHasType)
--
--         univ : B ∶ _ 𝒰 ∈ var x ∶ A ∷ _ ∷ Γ
--         univ = there A∶𝒰
--
--         type : var x₁ ∶ B ∈ var x ∶ A ∷ _ ∷ Γ
--         type = there x∶A
-- Wkg₁ (K ∷ Γ) [] A B b x x-fresh x-allFresh P (transport-∶ Q ())
-- Wkg₁ Γ (.(var _ ∶ _) ∷ Δ) A B .(var x₁) x x-fresh x-allFresh P
--     (Vble (ctx-EXT hasUniv freshInType allFresh allOfHasType) A∶𝒰 x₁ x∶A)
--     = Vble ctx univ x₁ type
--     where
--         ctx : CTX (_ ∷ Δ ++ var x ∶ A ∷ Γ)
--         ctx = ctx-EXT {! P !} freshInType {!  !} {!   !} -- ctx-EXT P x-fresh x-allFresh (tt ∷ allOfHasType)
--
--         univ : B ∶ _ 𝒰 ∈ _ ∷ Δ ++ var x ∶ A ∷ Γ
--         univ = {!  A∶𝒰  !}
--
--         type : var x₁ ∶ B ∈ _ ∷ Δ ++ var x ∶ A ∷ Γ
--         type = {!   !}
-- Wkg₁ Γ (K ∷ Δ) A B b x x-fresh x-allFresh P (transport-∶ Q ())


-- ⊢-∷ : ∀ {J} Γ K → Γ ⊢ K → J ∷ Γ ⊢ K
-- ⊢-∷ Γ (.(var x) ∶ A) (Vble isCTX A∶𝒰 x x∶A) = {!   !}
-- ⊢-∷ Γ (a ∶ A) (transport-∶ P P₁) = transport-∶ (⊢-∷ Γ (a ∶ _) P) (⊢-∷ Γ (_ ≣ A ∶ _ 𝒰) P₁)
-- ⊢-∷ Γ (a ≣ .a ∶ A) (≣-refl P) = ≣-refl (⊢-∷ Γ (a ∶ A) P)
-- ⊢-∷ Γ (a ≣ b ∶ A) (≣-sym P) = ≣-sym (⊢-∷ Γ (b ≣ a ∶ A) P)
-- ⊢-∷ Γ (a ≣ b ∶ A) (≣-trans P P₁) = ≣-trans (⊢-∷ Γ (a ≣ _ ∶ A) P) (⊢-∷ Γ (_ ≣ b ∶ A) P₁)
-- ⊢-∷ Γ (a ≣ b ∶ A) (transport-≣ P P₁) = transport-≣ (⊢-∷ Γ (a ≣ b ∶ _) P) (⊢-∷ Γ (_ ≣ A ∶ _ 𝒰) P₁)
-- ⊢-∷ Γ (A ∶ zero 𝒰) ()
-- ⊢-∷ Γ (A ∶ suc 𝒾 𝒰) (𝒰-CUMUL P) = 𝒰-CUMUL (⊢-∷ Γ (A ∶ 𝒾 𝒰) P)
-- ⊢-∷ Γ (A ≣ B ∶ 𝒾 𝒰) ()
--
-- ⊆-empty : ∀ {a} {A : Set a} (x : A) (xs : List A) → x ∷ xs ⊈ []
-- ⊆-empty x xs P with P {x} (here refl)
-- ⊆-empty x xs P | ()
--
-- test : ∀ Γ Δ L → Γ ⊆ Δ
--     → Γ ⊢ L
--     → Δ ⊢ L
-- test []      []      L P Q = Q
-- test []      (K ∷ Δ) L P Q = ⊢-∷ Δ L (test [] Δ L (λ {x} → λ ()) Q)
-- test (J ∷ Γ) []      L P Q = ⊥-elim (⊆-empty J Γ P)
-- test (J ∷ Γ) (K ∷ Δ) L P Q = {! test (J ∷ Γ) Δ L   !}
--
-- isCTX-lemma : ∀ Γ Δ A a x
--     → CTX Γ
--     → CTX (Δ ++ var x ∶ A ∷ Γ)
--     → var a ∶ A ∈ Γ
--     → CTX ((Δ ++ Γ) [ var a / x ]C)
-- isCTX-lemma Γ [] A a x CTX-A (ctx-EXT hasUniv (fresh ∷ allFresh) allOfHasType) a∶A
--     = subst CTX (PropEq.sym (CTX-subst-fresh Γ allFresh)) CTX-A
-- isCTX-lemma Γ (var k ∶ K ∷ Δ) A a x CTX-A (ctx-EXT hasUniv freshInType allFresh allOfHasType) a∶A with x ≟str k
-- isCTX-lemma Γ (var k ∶ K ∷ Δ) A a x CTX-A (ctx-EXT hasUniv (fresh ∷ allFresh) allOfHasType) a∶A | yes p
--     = contradiction (sym p) (CTX-fresh Γ Δ allFresh)
-- isCTX-lemma Γ (var k ∶ K ∷ Δ) A a x CTX-A (ctx-EXT hasUniv ((fresh-k , fresh-K) ∷ allFresh) allOfHasType) a∶A | no ¬p
--     = ctx-EXT univ {!   !} type
--     where
--         open import Function.Related
--         open EquationalReasoning
--
--         prop : Δ ++ (var x ∶ A) ∷ Γ ≡ (Δ ++ (var x ∶ A) ∷ Γ) [ var a / x ]C
--         prop = {!   !}
--
--         univ : (Δ ++ Γ) [ var a / x ]C ⊢ K [ var a / x ] ∶ _ 𝒰
--         univ = (
--                 Δ ++ (var x ∶ A) ∷ Γ ⊢ K ∶ _ 𝒰
--             ≡⟨ cong₂ (λ v w → v ⊢ w ∶ _ 𝒰)
--                 (PropEq.sym (C-subst-fresh allFresh))
--                 (PropEq.sym (subst-fresh fresh-K))
--             ⟩
--                 (Δ ++ (var x ∶ A) ∷ Γ) [ var a / x ]C ⊢ K [ var a / x ] ∶ _ 𝒰
--             ∼⟨ {! ⊢-nub Γ Δ a∶A   !} ⟩
--                 ((Δ ++ Γ) [ var a / x ]C ⊢ K [ var a / x ] ∶ _ 𝒰)
--             ∎) hasUniv
--         type : All ({!   !} k) ((Δ ++ Γ) [ var a / x ]C)
--         type = {! ? ∷ ?  !}
--
--          -- (Δ ++ Γ) [ var a / x ]C ≡ var v ∶ T ∷ E
--          -- var v ∶ T ∷ E ⊢
--
--         -- (Δ ++ var x ∶ A ∷ Γ) ≡ ((Δ ++ Γ) [ var a / x ]C)
--
-- -- isCTX-lemma Γ (var k ∶ K ∷ []) A a x CTX-A (ctx-EXT hasUniv (ctx ofHasType fresh ∷ allCTX)) a∶A | no ¬p
-- --     = ctx-EXT univ type
-- --     where
-- --         open import Function.Related
-- --         open EquationalReasoning
-- --
-- --         univ : Γ [ var a / x ]C ⊢ K [ var a / x ] ∶ _ 𝒰
-- --         univ = (
-- --                 (var x ∶ A) ∷ Γ ⊢ K ∶ _ 𝒰
-- --             ∼⟨ {!   !} ⟩
-- --                 {! a∶A  !}
-- --             ∼⟨ {!   !} ⟩
-- --                 {!   !}
-- --             ∼⟨ {!   !} ⟩
-- --                 {!   !}
-- --             ∼⟨ {!   !} ⟩
-- --                 (Γ [ var a / x ]C ⊢ K [ var a / x ] ∶ _ 𝒰)
-- --             ∎) hasUniv
-- --         type : All (IsCTX k) (Γ [ var a / x ]C)
-- --         type = {! allCTX  !}
-- --     -- CTX-subst-fresh
-- -- isCTX-lemma Γ (var k ∶ K ∷ L ∷ Δ) A a x CTX-A (ctx-EXT hasUniv (ctx ofHasType fresh ∷ allCTX)) a∶A | no ¬p
-- --     = ctx-EXT {!   !} {!   !}
--     -- = subst CTX eq (ctx-EXT hasUniv allCTX)
--     -- -- -- allCTX : All (IsCTX k) (Δ ++ var x ∶ A ∷ Γ)
--     -- --
--     -- --
--     -- where
--     --     eq : var k ∶ K ∷ Δ ++ var x ∶ A ∷ Γ ≡ (var k ∶ K [ var a / x ]) ∷ (Δ ++ Γ) [ var a / x ]C
--     --     eq = {!   !}
--
-- -- Subst₁ : ∀ Γ Δ A B {a} {b} x
-- --     →                   Γ ⊢ a           ∶ A             -- JA
-- --     →  Δ ++ var x ∶ A ∷ Γ ⊢ b           ∶ B             -- JB
-- --     → (Δ ++ Γ) [ a / x ]C ⊢ b [ a / x ] ∶ B [ a / x ]
-- -- Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) (Vble CTX-B B∶𝒰 b b∶B) with observe Γ Δ a∶A CTX-B
-- -- Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) (Vble CTX-B B∶𝒰 b b∶B) | observation v T E eq with x ≟str b
-- -- Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) (Vble CTX-B B∶𝒰 b b∶B) | observation v T E eq | yes p
-- --     = Vble isCTX univ a type
-- --     where
-- --         open import Function.Related
-- --         open EquationalReasoning
-- --
-- --         -- eq : (Δ ++ Γ) [ var a / x ]C ≡ var v ∶ T ∷ E
-- --         -- eq = ?
-- --
-- --         cc : {!   !}
-- --         cc = {!   !}
-- --
-- --         isCTX : CTX ((Δ ++ Γ) [ var a / x ]C)
-- --         isCTX = isCTX-lemma Γ Δ A a x CTX-A CTX-B a∶A
-- --
-- --         univ : B [ var a / x ] ∶ _ 𝒰 ∈ (Δ ++ Γ) [ var a / x ]C
-- --         univ = (
-- --                 B ∶ _ 𝒰 ∈ Δ ++ var x ∶ A ∷ Γ
-- --             ∼⟨ J-subst-mono (Δ ++ var x ∶ A ∷ Γ) (B ∶ _ 𝒰) ⟩
-- --                 B [ var a / x ] ∶ _ 𝒰 ∈  (Δ ++ var x ∶ A ∷ Γ) [ var a / x ]C
-- --             ∼⟨ C-subst-nub Γ Δ a∶A ⟩
-- --                 B [ var a / x ] ∶ _ 𝒰 ∈ (Δ ++ Γ) [ var a / x ]C
-- --             ∎) B∶𝒰
-- --
-- --         type : var a ∶ B [ var a / x ] ∈ (Δ ++ Γ) [ var a / x ]C
-- --         type = (
-- --                 var b ∶ B ∈ Δ ++ var x ∶ A ∷ Γ
-- --             ≡⟨ cong (λ w → var w ∶ B ∈ Δ ++ var x ∶ A ∷ Γ) (PropEq.sym p) ⟩
-- --                 var x ∶ B ∈ Δ ++ var x ∶ A ∷ Γ
-- --             ∼⟨ J-subst-mono (Δ ++ var x ∶ A ∷ Γ) (var x ∶ B) ⟩
-- --                 (var x ∶ B) [ var a / x ]J ∈ (Δ ++ var x ∶ A ∷ Γ) [ var a / x ]C
-- --             ≡⟨ cong (λ w → w ∈ (Δ ++ var x ∶ A ∷ Γ) [ var a / x ]C) (a∶A-subst B (var a) x) ⟩
-- --                 var a ∶ B [ var a / x ] ∈ (Δ ++ var x ∶ A ∷ Γ) [ var a / x ]C
-- --             ∼⟨ C-subst-nub Γ Δ a∶A ⟩
-- --                 var a ∶ B [ var a / x ] ∈ (Δ ++ Γ) [ var a / x ]C
-- --             ∎) b∶B
-- -- Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) (Vble CTX-B B∶𝒰 b b∶B) | observation v T E eq | no ¬p
-- --     = Vble isCTX univ b type
-- --     where
-- --         open import Function.Related
-- --         open EquationalReasoning
-- --
-- --         isCTX : CTX ((Δ ++ Γ) [ var a / x ]C)
-- --         isCTX = isCTX-lemma Γ Δ A a x CTX-A CTX-B a∶A
-- --
-- --         univ : B [ var a / x ] ∶ _ 𝒰 ∈ (Δ ++ Γ) [ var a / x ]C
-- --         univ = (
-- --                 B ∶ _ 𝒰 ∈ Δ ++ var x ∶ A ∷ Γ
-- --             ∼⟨ J-subst-mono (Δ ++ var x ∶ A ∷ Γ) (B ∶ _ 𝒰) ⟩
-- --                 B [ var a / x ] ∶ _ 𝒰 ∈  (Δ ++ var x ∶ A ∷ Γ) [ var a / x ]C
-- --             ∼⟨ C-subst-nub Γ Δ a∶A ⟩
-- --                 B [ var a / x ] ∶ _ 𝒰 ∈ (Δ ++ Γ) [ var a / x ]C
-- --             ∎) B∶𝒰
-- --
-- --         type : var b ∶ B [ var a / x ] ∈ (Δ ++ Γ) [ var a / x ]C
-- --         type = (
-- --                 var b ∶ B ∈ Δ ++ var x ∶ A ∷ Γ
-- --             ∼⟨ J-subst-mono (Δ ++ var x ∶ A ∷ Γ) (var b ∶ B) ⟩
-- --                 var b [ var a / x ] ∶ B [ var a / x ] ∈ (Δ ++ var x ∶ A ∷ Γ) [ var a / x ]C
-- --             ≡⟨ cong (λ w → w ∶ B [ var a / x ] ∈ (Δ ++ var x ∶ A ∷ Γ) [ var a / x ]C) (subst-fresh ¬p) ⟩
-- --                 var b ∶ B [ var a / x ] ∈ (Δ ++ var x ∶ A ∷ Γ) [ var a / x ]C
-- --             ∼⟨ C-subst-nub Γ Δ a∶A ⟩
-- --                 var b ∶ B [ var a / x ] ∈ (Δ ++ Γ) [ var a / x ]C
-- --             ∎) b∶B
-- -- -- Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) Q with (Δ ++ Γ) [ var a / x ]C | inspect (λ C → C [ var a / x ]C) (Δ ++ Γ)
-- -- -- Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) Q | [] | inspect[ eq ] = contradiction a∶A (Subst₁-empty-context Γ Δ A eq)
-- -- -- Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) (Vble CTX-B B∶𝒰 b b∶B) | a₁ ∶ A₁ ∷ E | inspect[ eq ] = {! a∶A  !}
-- -- -- Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) (Vble CTX-B B∶𝒰 b b∶B) | a₁ ≣ b₁ ∶ A₁ ∷ E | inspect[ eq ] = {!   !}
-- -- -- Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) (Vble CTX-B B∶𝒰 b b∶B) | A₁ ∶ 𝒾 𝒰 ∷ E | inspect[ eq ] = {!   !}
-- -- -- Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) (Vble CTX-B B∶𝒰 b b∶B) | A₁ ≣ B₁ ∶ 𝒾 𝒰 ∷ E | inspect[ eq ] = {!   !}
-- -- Subst₁ Γ Δ A B x (Vble CTX-A A∶𝒰 a a∶A) (transport-∶ Q Q₁) = {!   !}
-- -- Subst₁ Γ Δ A B x (transport-∶ P P₁) Q = {!   !}
