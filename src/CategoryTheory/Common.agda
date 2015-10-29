{-# OPTIONS --type-in-type #-}

module CategoryTheory.Common where

-- synonym for the type of types
Typeᵀ : Set
Typeᵀ = Set

_↠_ : Typeᵀ → Typeᵀ → Typeᵀ
ob ↠ U = ob → ob → U

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
_−ᴱ→_ : relᵀ Endoᵀ
F −ᴱ→ G = {x : Typeᵀ} → F x −ᵀ→ G x

-- dependent product
𝝥 : {Base : Typeᵀ} → preᵀ (preᵀ Base)
𝝥 {Base} Fiber = (base : Base) → Fiber base

-- dependent sum
data 𝝨 {Base : Typeᵀ} : preᵀ (preᵀ Base) where
  _∷_ : {Fiber : preᵀ Base} →
      (base : Base) →
      (fiber : Fiber base) →
      𝝨 Fiber

-- synomym for dependent lambda syntax
infixr -100 λ-dep
λ-dep : {A : Typeᵀ} → {B : preᵀ A} → endoᵀ (𝝥 B)
λ-dep f = f
syntax λ-dep (λ a → b) = a ↦ b

-- synomym for non-dependent lambda syntax
infixr -100 λ-mor
λ-mor : {A B : Typeᵀ} → endoᵀ (A −ᵀ→ B)
λ-mor f = f
syntax λ-mor (λ a → b) = a ⟼ b

-- declare type in subexpression: "the A a"
the : 𝝥 endoᵀ
the A a = a
