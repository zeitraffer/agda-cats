{-# OPTIONS --type-in-type --copatterns #-}

module Structs.PullbackDef where

open import Structs.RelationDef

record Pullback 
    {L R B : Set}
    ⦃ rel : Relation-Class B ⦄
    (l : L ⟶ B)
    (r : R ⟶ B) :
    Set
  where
    constructor MkPullback
    field
      pbLeft : L
      pbRight : R
      l=r : l pbLeft ⟶ r pbRight
open Pullback public

