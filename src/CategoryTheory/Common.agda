{-# OPTIONS --type-in-type #-}

module CategoryTheory.Common where

-- synonym for the type of types
Typeᵀ : Set
Typeᵀ = Set

infix 0 _↠_
_↠_ : Typeᵀ → Typeᵀ → Typeᵀ
ob ↠ U = ob → ob → U

infix 0 _⇸_
_⇸_ : Typeᵀ → Typeᵀ → Typeᵀ
source ⇸ target = source → target → Typeᵀ

-- endomorphisms in "Type"
endoᵀ : Typeᵀ → Typeᵀ
endoᵀ A = A → A

-- plain endofunctors
Endoᵀ : Typeᵀ
Endoᵀ = endoᵀ Typeᵀ

-- predicate (plain presheaf)
preᵀ : Endoᵀ
preᵀ A = A → Typeᵀ

-- plain relation
relᵀ : Endoᵀ
relᵀ A = A ↠ Typeᵀ

-- relation over Type
Relᵀ : Typeᵀ
Relᵀ = relᵀ Typeᵀ

-- morphism in "Type"
infix -10 _−ᵀ→_
_−ᵀ→_ : Relᵀ
a −ᵀ→ b = a → b

-- exponentiation in "Type"
infixr 10 _−ᵀ⊸_
_−ᵀ⊸_ : Relᵀ
a −ᵀ⊸ b = a → b

-- morphisms between endofunctors
_−ᴾ→_ : {Base : Typeᵀ} → relᵀ (preᵀ Base)
_−ᴾ→_ {Base} F G = {x : Base} → F x −ᵀ→ G x

-- dependent product
𝝥 : {Base : Typeᵀ} → preᵀ (preᵀ Base)
𝝥 {Base} Fiber = (base : Base) → Fiber base

-- dependent product (implicit)
𝝥' : {Base : Typeᵀ} → preᵀ (preᵀ Base)
𝝥' {Base} Fiber = {base : Base} → Fiber base

-- dependent sum
infixr -99 _,_
record 𝝨 {Base : Typeᵀ} (Fiber : preᵀ Base) : Typeᵀ
  where
    constructor _,_
    field base : Base
    field fiber : Fiber base

-- synomym for dependent lambda syntax
infixr -100 λ-dep
λ-dep : {A : Typeᵀ} → {B : preᵀ A} → endoᵀ (𝝥 B)
λ-dep f = f
syntax λ-dep (λ a → b) = a ↦ b

-- synomym for dependent lambda syntax (implicit)
infixr -100 λ-dep'
λ-dep' : {A : Typeᵀ} → {B : preᵀ A} → 𝝥 B → 𝝥' B
λ-dep' f {a} = f a
syntax λ-dep' (λ a → b) = a ↦' b

-- synomym for non-dependent lambda syntax
infixr -100 λ-mor
λ-mor : {A B : Typeᵀ} → endoᵀ (A −ᵀ→ B)
λ-mor f = f
syntax λ-mor (λ a → b) = a ⟼ b

-- declare type in subexpression: "the A a"
the : 𝝥 endoᵀ
the A a = a

infix -100 _≡_
data _≡_ {X : Typeᵀ} : relᵀ X where
    Refl : {x : X} → x ≡ x

_−ᴬ→_ : {A B : Typeᵀ} → relᵀ (A ⇸ B)
_−ᴬ→_ {A} {B} _⇒₁_ _⇒₂_ = {a : A} → {b : B} → (a ⇒₁ b) −ᵀ→ (a ⇒₂ b)

_−ᴬ⊸_ : {A B C : Typeᵀ} → (B ⇸ C) → (A ⇸ C) → (A ⇸ B)
_−ᴬ⊸_ {A} {B} {C} _ᵇ⇒ᶜ_ _ᵃ⇒ᶜ_ a b = {c : C} → (b ᵇ⇒ᶜ c) −ᵀ→ (a ᵃ⇒ᶜ c)

_⟜ᴬ−_ : {A B C : Typeᵀ} → (C ⇸ A) → (C ⇸ B) → (A ⇸ B)
_⟜ᴬ−_ {A} {B} {C} _ᶜ⇒ᵃ_ _ᶜ⇒ᵇ_ a b = {c : C} → (c ᶜ⇒ᵃ a) −ᵀ→ (c ᶜ⇒ᵇ b)
