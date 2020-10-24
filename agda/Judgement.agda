module Judgement where

open import Data.List
open import Data.List.All as All hiding (map)
open import Data.Nat
open import Data.Product hiding (map)
open import Data.String using (String) renaming (_≟_ to _≟str_)

open import Relation.Nullary
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to inspect[_])

--------------------------------------------------------------------------------
--  Terms
--------------------------------------------------------------------------------

Variable : Set
Variable = String

data Term : Set where
    var : String → Term

_#_ : Variable → Term → Set
variable # var x = variable ≢ x

-- Term substitution
infix 200 _[_/_]
_[_/_] : Term → Term → Variable → Term
var x [ expr / variable ] with variable ≟str x
var x [ expr / variable ] | yes p = expr
var x [ expr / variable ] | no ¬p = var x

subst-fresh : ∀ {term variable expr}
    → variable # term
    → term [ expr / variable ] ≡ term
subst-fresh {var x} {variable} fresh with variable ≟str x
subst-fresh {var x} {variable} fresh | yes p = contradiction p fresh
subst-fresh {var x} {variable} fresh | no ¬p = refl

--------------------------------------------------------------------------------
--  Judgements
--------------------------------------------------------------------------------

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

_#J_ : Variable → Judgement → Set
variable #J (    a ∶ A)   = variable # a × variable # A
variable #J (a ≣ b ∶ A)   = variable # a × variable # b × variable # A
variable #J (    A ∶ 𝒾 𝒰) = variable # A
variable #J (A ≣ B ∶ 𝒾 𝒰) = variable # A × variable # B

_T#J_ : Term → Judgement → Set
var x T#J J = x #J J

_♯J_ : Judgement → Judgement → Set
(    a ∶ A) ♯J J = a T#J J × A T#J J
(a ≣ b ∶ A) ♯J J = a T#J J × b T#J J × A T#J J
(    A ∶ 𝒾 𝒰) ♯J J = A T#J J
(A ≣ B ∶ 𝒾 𝒰) ♯J J = A T#J J × B T#J J

J-subst-fresh : ∀ {judgement variable expr}
    → variable #J judgement
    → judgement [ expr / variable ]J ≡ judgement
J-subst-fresh {      a ∶ A} (a-fresh , A-fresh) = cong₂ _∶_ (subst-fresh a-fresh) (subst-fresh A-fresh)
J-subst-fresh {a ≣ b ∶   A} (a-fresh , b-fresh , A-fresh) =
    begin
        a [ _ / _ ] ≣ b [ _ / _ ] ∶ A [ _ / _ ]
    ≡⟨ cong (λ x → a [ _ / _ ] ≣ b [ _ / _ ] ∶ x) (subst-fresh A-fresh) ⟩
        a [ _ / _ ] ≣ b [ _ / _ ] ∶ A
    ≡⟨ cong₂ (λ x y → x ≣ y ∶ A) (subst-fresh a-fresh) (subst-fresh b-fresh) ⟩
        a ≣ b ∶ A
    ∎
    where
        open PropEq.≡-Reasoning
J-subst-fresh {    A ∶ 𝒾 𝒰} A-fresh = cong (λ x → x ∶ 𝒾 𝒰) (subst-fresh A-fresh)
J-subst-fresh {A ≣ B ∶ 𝒾 𝒰} (A-fresh , B-fresh) = cong₂ (λ x y → x ≣ y ∶ 𝒾 𝒰) (subst-fresh A-fresh) (subst-fresh B-fresh)



--------------------------------------------------------------------------------
--  Context
--------------------------------------------------------------------------------

Context : Set
Context = List Judgement

infix 200 _[_/_]C
_[_/_]C : Context → Term → Variable → Context
context [ expr / x ]C = map (λ j → j [ expr / x ]J) context

_#C_ : Variable → Context → Set
x #C Γ = All (_#J_ x) Γ

_♯C_ : Judgement → Context → Set
J ♯C Γ = All (_♯J_ J) Γ

open import Data.List.Any
open import Data.List.Any.Membership.Propositional
open import Data.List.Any.Properties using (∷↔)

J-subst-mono : ∀ Γ J {e x}
    →  J             ∈ Γ
    → (J [ e / x ]J) ∈ Γ [ e / x ]C
J-subst-mono _ J (here px) = here (cong ((λ w → w [ _ / _ ]J)) px)
J-subst-mono _ J (there P) = there (J-subst-mono _ J P)

C-subst-mono : ∀ Γ Δ {e x}
    → Γ            ⊆ Δ
    → Γ [ e / x ]C ⊆ Δ [ e / x ]C
C-subst-mono []      Δ P ()
C-subst-mono (J ∷ Γ) Δ P (here refl) = J-subst-mono Δ J (P (here refl))
C-subst-mono (J ∷ Γ) Δ P (there Q)   = C-subst-mono Γ Δ (
    begin
        Γ
    ⊆⟨ there ⟩
        J ∷ Γ
    ⊆⟨ P ⟩
        Δ
    ∎) Q
    where open ⊆-Reasoning


self-subst : ∀ a x → a ≡ a [ a / x ]
self-subst (var x') x with x ≟str x | x ≟str x'
self-subst (var x') x | yes p | yes q = refl
self-subst (var x') x | yes p | no ¬q = refl
self-subst (var x') x | no ¬p | yes q = refl
self-subst (var x') x | no ¬p | no ¬q = refl

C-subst-fresh : ∀ {Γ variable expr}
    → All (_#J_ variable) Γ
    → Γ [ expr / variable ]C ≡ Γ
C-subst-fresh {[]}    {variable} {expr} pxs = refl
C-subst-fresh {J ∷ Γ} {variable} {expr} (px ∷ pxs)
    = cong₂ _∷_ (J-subst-fresh px) (C-subst-fresh pxs)

a∶A-subst : ∀ A a x → (var x ∶ A) [ a / x ]J ≡ a ∶ A [ a / x ]
a∶A-subst A a x with x ≟str x
a∶A-subst A a x | yes p = refl
a∶A-subst A a x | no ¬p = contradiction refl ¬p

nub : {xs : Context} {y : Judgement} → y ∈ xs → y ∷ xs ⊆ xs
nub {[]}     ()   x∈y∷xs
nub {x ∷ xs} y∈xs (here refl) = y∈xs
nub {x ∷ xs} y∈xs (there p)   = p

weakening : ∀ {a} {A : Set a}
    → (xs ys : List A) → (y : A)
    → xs ++ ys ⊆ xs ++ y ∷ ys
weakening xs ys y P = ++-cong {xs₁ = xs} (λ w → w) there P
    where
        open import Data.List.Any.BagAndSetEquality using (++-cong)

C-subst-++ : ∀ {e x} Γ Δ
    → (Γ ++ Δ) [ e / x ]C ≡ Γ [ e / x ]C ++ Δ [ e / x ]C
C-subst-++ {e} {x} Γ Δ = map-++-commute (λ w → w [ e / x ]J) Γ Δ
    where
        open import Data.List.Properties using (map-++-commute)

C-subst-nub : ∀ Γ Δ {A a x}
    → a ∶ A ∈ Γ
    → (Δ ++ var x ∶ A ∷ Γ) [ a / x ]C ⊆ (Δ ++ Γ) [ a / x ]C
C-subst-nub []      Δ             ()
C-subst-nub (J ∷ Γ) Δ {A} {a} {x} P =
    begin
        (Δ ++ var x ∶ A ∷ J ∷ Γ) [ a / x ]C
    ≡⟨ C-subst-++ Δ (var x ∶ A ∷ J ∷ Γ) ⟩
        Δ [ a / x ]C ++ (var x ∶ A ∷ J ∷ Γ) [ a / x ]C
    ⊆⟨ ++-cong {xs₁ = Δ [ a / x ]C} (λ w → w) (
        begin
            (var x ∶ A ∷ J ∷ Γ) [ a / x ]C
        ≡⟨ refl ⟩
            (var x ∶ A) [ a / x ]J ∷ (J ∷ Γ) [ a / x ]C
        ≡⟨ cong (λ p → p ∷ (J ∷ Γ) [ a / x ]C) (a∶A-subst A a x) ⟩
            a ∶ A [ a / x ] ∷ (J ∷ Γ) [ a / x ]C
         ≡⟨ cong (λ p → p ∶ A [ a / x ] ∷ (J ∷ Γ) [ a / x ]C) (self-subst a x) ⟩
            (a ∶ A ∷ J ∷ Γ) [ a / x ]C
        ⊆⟨ C-subst-mono (a ∶ A ∷ J ∷ Γ) (J ∷ Γ) (nub P) ⟩
            (J ∷ Γ) [ a / x ]C
        ∎
    )⟩
        Δ [ a / x ]C ++ (J ∷ Γ) [ a / x ]C
    ≡⟨ sym (C-subst-++ Δ (J ∷ Γ)) ⟩
        (Δ ++ J ∷ Γ) [ a / x ]C
    ∎
    where
        open ⊆-Reasoning
        open import Data.List.Any.BagAndSetEquality using (++-cong)
-- module EquationalReasoning where

  -- _≡⟨_⟩_ : ∀ {k ℓ z} (X : Set ℓ) {Y : Set ℓ} {Z : Set z} →
  --          X ≡ Y → Y ∼[ k ] Z → X ∼[ k ] Z
  -- X ≡⟨ X≡Y ⟩ Y⇔Z = X ∼⟨ ≡⇒ X≡Y ⟩ Y⇔Z

-- test : ∀ Γ Δ {e x}
--     → Γ            ⊆ Δ
--     → Γ [ e / x ]C ⊆ Δ [ e / x ]C
-- test Γ Δ {e} {x} Γ⊆Δ =
--         Any _ (Γ [ e / x ]C)
--     ∼⟨ {!   !} ⟩
--         Any _ (Δ [ e / x ]C)
--     ∎
--     where
--         open import Function.Related
--         open EquationalReasoning
-- C-subst-mono
