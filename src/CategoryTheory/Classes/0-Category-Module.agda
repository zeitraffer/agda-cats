{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Classes.0-Category-Module where

open import CategoryTheory.Common-Module
open import CategoryTheory.Operations.TypeSpan-Module
open import CategoryTheory.Operations.PathSpan-Module
open import CategoryTheory.Classes.TypeSpan-Module
open import CategoryTheory.Instances.Type-TypeEndoSpan-Module
open import CategoryTheory.Instances.TypeSpan-TypeEndoSpan-Module

--------------------------------------
-- `0-Category-Class` to be a preorder
--

record 0-Category-Class 
    {X : Type} 
    (relC : TypeEndoSpan-Class X) 
    : Type 
  where
    constructor Mk
    rel = get relC
    field
      paste : PathSpan rel ⟶ rel

⁰id : 
    {X : Type} → 
    {{rel : TypeEndoSpan-Class X}} → 
    {{cat : 0-Category-Class rel}} → 
    {x : X} → 
    x ⟶ x
⁰id {{rel}} {{cat}} = 0-Category-Class.paste cat []

⁰mul : 
    {X : Type} → 
    {{rel : TypeEndoSpan-Class X}} → 
    {{cat : 0-Category-Class rel}} → 
    {a b c : X} → 
    b ⟶ c → a ⟶ b → a ⟶ c 
⁰mul {{rel}} {{cat}} f g = 0-Category-Class.paste cat (f , g , [])
