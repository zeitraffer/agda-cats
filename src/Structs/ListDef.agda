{-# OPTIONS --type-in-type --copatterns #-}

module Structs.ListDef where

open import Structs.RelationDef

data List (X : Type) : Type 
  where
    Nil : List X
    _∷_ : X → List X → List X

appendList : {X : Type} → List X → List X → List X
appendList Nil ys = ys
appendList (x ∷ xs) ys = x ∷ appendList xs ys

-- neutralListLeft : {X : Type} → (xs : List X) → appendList Nil ys

returnList : {X : Type} → X ⟶ List X
returnList x = x ∷ Nil

flattenList : {X : Type} → List (List X) ⟶ List X
flattenList Nil = Nil
flattenList (Nil ∷ tail) = flattenList tail
flattenList ((h ∷ t) ∷ tail) = h ∷ flattenList (t ∷ tail)

mapList : {A B : Type} → (A ⟶ B) ⟶ (List A ⟶ List B)
mapList f Nil = Nil
mapList f (h ∷ t) = f h ∷ mapList f t

data _⟶*_ 
    {X : Type} ⦃ relX : Relation-Class X ⦄ : 
    (src dst : List X) → Type
  where
    Nil : 
        Nil ⟶* Nil
    _∷_ : 
        {x x' : X} → {xs xs' : List X} → 
        (x ⟶ x') → (xs ⟶* xs') → 
        (x ∷ xs) ⟶* (x' ∷ xs')

instance 
  List-Relation : {X : Type} → ⦃ relX : Relation-Class X ⦄ → Relation-Class (List X)
  get-Relation List-Relation = _⟶*_


