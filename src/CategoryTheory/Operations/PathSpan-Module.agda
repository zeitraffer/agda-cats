{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Operations.PathSpan-Module where

open import CategoryTheory.Common-Module
open import CategoryTheory.Operations.TypeSpan-Module

--------------------------------------
-- `PathSpan` to be a transitive closure
--

infixr 0 _,_

data PathSpan
    {X : Type}
    (rel : TypeSpan-Type X X) :
    TypeSpan-Type X X
  where
    [] :
        {x : X} →
        PathSpan rel x x
    _,_ :
        {a b c : X} →
        rel b c →
        PathSpan rel a b →
        PathSpan rel a c
