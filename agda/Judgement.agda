module Judgement where

open import Data.List
open import Data.Product hiding (map)
open import Data.Nat
open import Data.String using (String) renaming (_≟_ to _≟str_)
open import Relation.Nullary
open import Relation.Nullary.Negation using (contradiction)
-- open import Relation.Nullary.Decidable hiding (map)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to inspect[_])

Variable : Set
Variable = String

data Term : Set where
    var : String → Term

_FreshIn_ : Variable → Term → Set
variable FreshIn var x = variable ≢ x

-- Term substitution
infix 200 _[_/_]
_[_/_] : Term → Term → Variable → Term
var x [ expr / variable ] with variable ≟str x
var x [ expr / variable ] | yes p = expr
var x [ expr / variable ] | no ¬p = var x

fresh-substitution : ∀ {term variable expr}
    → variable FreshIn term
    → term [ expr / variable ] ≡ term
fresh-substitution {var x} {variable} fresh with variable ≟str x
fresh-substitution {var x} {variable} fresh | yes p = contradiction p fresh
fresh-substitution {var x} {variable} fresh | no ¬p = refl

-- Four kinds of Judgements
infix 100 _∶_ _≣_∶_ _∶_𝒰 _≣_∶_𝒰
data Judgement : Set where
    _∶_     : (a   A : Term) → Judgement
    _≣_∶_   : (a b A : Term) → Judgement
    _∶_𝒰   : (A   : Term) → (𝒾 : ℕ) → Judgement
    _≣_∶_𝒰 : (A B : Term) → (𝒾 : ℕ) → Judgement

-- Judgement substitution
infix 200 _[_/_]J
_[_/_]J : Judgement → Term → Variable → Judgement
(    a ∶ A)   [ expr / x ]J = a [ expr / x ] ∶ A [ expr / x ]
(a ≣ b ∶ A)   [ expr / x ]J = a [ expr / x ] ≣ b [ expr / x ] ∶ A [ expr / x ]
(    A ∶ 𝒾 𝒰) [ expr / x ]J = A [ expr / x ] ∶ 𝒾 𝒰
(A ≣ B ∶ 𝒾 𝒰) [ expr / x ]J = A [ expr / x ] ≣ B [ expr / x ] ∶ 𝒾 𝒰


    -- open import Membership Judgement

-- ++-context-substitution : ∀ {e x} Γ Δ → (Γ ++ Δ) [ e / x ]C ≋ Γ [ e / x ]C ++ Δ [ e / x ]C
-- ++-context-substitution {e} {x} Γ Δ = ≡→≋ (map-++-commute (λ w → w [ e / x ]J) Γ Δ)
--     where
--         open import Data.List.Properties using (map-++-commute)
--
Context : Set
Context = List Judgement

infix 200 _[_/_]C
_[_/_]C : Context → Term → Variable → Context
context [ expr / x ]C = map (λ j → j [ expr / x ]J) context

open import Data.List.All as All
open import Data.Unit
open import Data.Empty
open import Membership Judgement

judgement-substitution-mono : ∀ Γ J e x
    →  J             ∈ Γ
    → (J [ e / x ]J) ∈ Γ [ e / x ]C
judgement-substitution-mono Γ J e x (here  p) = here  (cong (λ w → w [ e / x ]J) p)
judgement-substitution-mono Γ J e x (there p) = there (judgement-substitution-mono _ J e x p)

context-substitution-mono : ∀ Γ Δ e x
    → Γ            ⊆ Δ
    → Γ [ e / x ]C ⊆ Δ [ e / x ]C
context-substitution-mono [] Δ e x P ()
context-substitution-mono (J ∷ Γ) Δ e x P (here refl) = judgement-substitution-mono Δ J e x (P (here refl))
context-substitution-mono (J ∷ Γ) Δ e x P (there Q) = context-substitution-mono Γ Δ e x (
    begin
        Γ
    ≤⟨ there ⟩
        J ∷ Γ
    ≤⟨ P ⟩
        Δ
    ∎) Q

self-substitution : ∀ a x → a ≡ a [ a / x ]
self-substitution (var x') x with x ≟str x | x ≟str x'
self-substitution (var x') x | yes p | yes q = refl
self-substitution (var x') x | yes p | no ¬q = refl
self-substitution (var x') x | no ¬p | yes q = refl
self-substitution (var x') x | no ¬p | no ¬q = refl

a∶A-substitution : ∀ A a x → (var x ∶ A) [ a / x ]J ≡ (a ∶ A) [ a / x ]J
a∶A-substitution A a x with x ≟str x
a∶A-substitution A a x | yes p = cong (λ w → w ∶ A [ a / x ]) (self-substitution a x)
a∶A-substitution A a x | no ¬p = contradiction refl ¬p

substitution-lemma1 : ∀ Γ A a x
    → a ∶ A ∈ Γ
    → (var x ∶ A ∷ Γ) [ a / x ]C ⊆ Γ [ a / x ]C
substitution-lemma1 []      A a x ()
substitution-lemma1 (J ∷ Γ) A a x P =
    begin
        (var x ∶ A ∷ (J ∷ Γ)) [ a / x ]C
    ≈⟨ ≋-refl ⟩
        (var x ∶ A) [ a / x ]J ∷ (J ∷ Γ) [ a / x ]C
    ≈⟨ ≡→≋ (cong (λ p → p ∷ (J ∷ Γ) [ a / x ]C) (a∶A-substitution A a x)) ⟩
        (a ∶ A ∷ J ∷ Γ) [ a / x ]C
    ≤⟨ context-substitution-mono (_ ∶ _ ∷ J ∷ Γ) (J ∷ Γ) a x (nub P) ⟩
        (J ∷ Γ) [ a / x ]C
    ∎

-- mutual
--
--     -- The item of Context should be of the form _∶_
--     -- and distinct from the supposedly fresh variable
--     CtxProp : Variable → Judgement → Set
--     CtxProp v (var x ∶ A)   = v ≢ x × v FreshIn A
--     CtxProp v (a ≣ b ∶ A)   = ⊥
--     CtxProp v (    A ∶ 𝒾 𝒰) = ⊥
--     CtxProp v (A ≣ B ∶ 𝒾 𝒰) = ⊥
--
--     data CTX : List Judgement → Set where
--         ctx-EMP : CTX []
--         ctx-EXT : ∀ {𝒾 Γ A x}
--             → Γ ⊢ A ∶ 𝒾 𝒰
--             → All (CtxProp x) Γ
--             → CTX ((var x ∶ A) ∷ Γ)
--
--     infix 3 _⊢_
--     data _⊢_ : Context → Judgement → Set where
--         Vble : ∀ {Γ 𝒾 A}
--             → CTX Γ
--             → A ∶ 𝒾 𝒰 ∈ Γ
--             → (x : Variable)
--             → var x ∶ A ∈ Γ
--             ------------------------------ Vble
--             → Γ ⊢ var x ∶ A
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
--         ≣-refl : ∀ {Γ A a}
--             → Γ ⊢ a ∶ A
--             ------------------------------
--             → Γ ⊢ a ≣ a ∶ A
--
--         ≣-sym : ∀ {Γ A a b}
--             → Γ ⊢ a ≣ b ∶ A
--             ------------------------------
--             → Γ ⊢ b ≣ a ∶ A
--
--         ≣-trans : ∀ {Γ A a b c}
--             → Γ ⊢ a ≣ b ∶ A
--             → Γ ⊢ b ≣ c ∶ A
--             ------------------------------
--             → Γ ⊢ a ≣ c ∶ A
--
--         transport-∶ : ∀ {Γ 𝒾 A B a}
--             → Γ ⊢ a ∶ A
--             → Γ ⊢ A ≣ B ∶ 𝒾 𝒰
--             ------------------------------
--             → Γ ⊢ a ∶ B
--
--         transport-≣ : ∀ {Γ 𝒾 A B a b}
--             → Γ ⊢ a ≣ b ∶ A
--             → Γ ⊢ A ≣ B ∶ 𝒾 𝒰
--             ------------------------------
--             → Γ ⊢ a ≣ b ∶ B
--
--         𝒰-CUMUL : ∀ {Γ 𝒾 A}
--             → Γ ⊢ A ∶     𝒾 𝒰
--             ------------------------------
--             → Γ ⊢ A ∶ suc 𝒾 𝒰
--
--
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
-- -- ctx-EXT : ∀ {𝒾 Γ A x}
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
--         hasType' = judgement-substitution-mono (var x ∶ A ∷ J ∷ Γ) (B ∶ _ 𝒰) (var a) x B∶𝒰
--
--         hasType : B [ var a / x ] ∶ _ 𝒰 ∈ (J ∷ Γ) [ var a / x ]C
--         hasType = substitution-lemma1 (J ∷ Γ) A (var a) x a∶A hasType' --
--
--         hasVar'' : (var b ∶ B) [ var a / x ]J ∈ (var x ∶ A ∷ J ∷ Γ) [ var a / x ]C
--         hasVar'' = judgement-substitution-mono (var x ∶ A ∷ J ∷ Γ) (var b ∶ B) (var a) x b∶B
--
--         lemma2 : (var b ∶ B) [ var a / x ]J ≡ var a ∶ B [ var a / x ]
--         lemma2 = Subst₁-lemma2 B a b x p
--
--         hasVar' : var a ∶ B [ var a / x ] ∈ (var x ∶ A ∷ J ∷ Γ) [ var a / x ]C
--         hasVar' = subst (λ w → w ∈ (var x ∶ A ∷ J ∷ Γ) [ var a / x ]C) lemma2 hasVar''
--         -- hasVar' : var a ∶ B [ var a / x ] ∈ (var x ∶ A ∷ J ∷ Γ) [ var a / x ]C
--         -- hasVar' = judgement-substitution-mono (var x ∶ A ∷ J ∷ Γ) {! var a ∶ B  !} (var a) x b∶B'
--         -- b ≡ x that's why we have 'var a ∶ ...'
--         hasVar : var a ∶ B [ var a / x ] ∈ (J ∷ Γ) [ var a / x ]C
--         hasVar = substitution-lemma1 (J ∷ Γ) A (var a) x a∶A hasVar'
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
--         hasType' = judgement-substitution-mono (var x ∶ A ∷ J ∷ Γ) (B ∶ _ 𝒰) (var a) x B∶𝒰
--
--         hasType : B [ var a / x ] ∶ _ 𝒰 ∈ (J ∷ Γ) [ var a / x ]C
--         hasType = substitution-lemma1 (J ∷ Γ) A (var a) x a∶A hasType'
--
--         hasVar'' : (var b ∶ B) [ var a / x ]J ∈ (var x ∶ A ∷ J ∷ Γ) [ var a / x ]C
--         hasVar'' = judgement-substitution-mono (var x ∶ A ∷ J ∷ Γ) (var b ∶ B) (var a) x b∶B
--         --
--         lemma2 : (var b ∶ B) [ var a / x ]J ≡ var b ∶ B [ var a / x ]
--         lemma2 = Subst₁-lemma3 B a b x ¬p
--
--         hasVar' : var b ∶ B [ var a / x ] ∈ (var x ∶ A ∷ J ∷ Γ) [ var a / x ]C
--         hasVar' = subst (λ w → w ∈ (var x ∶ A ∷ J ∷ Γ) [ var a / x ]C) lemma2 hasVar''
--
--         hasVar : var b ∶ B [ var a / x ] ∈ (J ∷ Γ) [ var a / x ]C
--         hasVar = substitution-lemma1 (J ∷ Γ) A (var a) x a∶A hasVar' -- substitution-lemma1 (J ∷ Γ) A (var a) x a∶A hasVar'
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
-- -- --         start = judgement-substitution-mono (Δ ++ var x ∶ A ∷ Γ) (_ ∶ _) a x Q
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
-- -- -- Subst₁ Γ Δ A B a b {x} (in-context P) (Vble Q) = in-context {! judgement-substitution-mono (Δ ++ var x ∶ A ∷ Γ) (_ ∶ _) a x   !}
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
