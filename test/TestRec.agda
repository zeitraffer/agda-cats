{-# OPTIONS --type-in-type --copatterns #-}

module TestRec where

Type : Set
Type = Set

infixr -10 λ-syntax
λ-syntax : {A B : Type} → (A → B) → (A → B)
λ-syntax f = f
syntax λ-syntax (λ x → B) = x ↦ B

---------------------------
-- definitions of type-classes

id : Type → Type
id = t ↦ t

fst : Type → Type → Type
fst = a ↦ b ↦ a

snd : Type → Type → Type
snd = a ↦ b ↦ b

---------------------------
