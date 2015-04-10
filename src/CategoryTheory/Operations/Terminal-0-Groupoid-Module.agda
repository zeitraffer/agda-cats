{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Operations.Terminal-0-Groupoid-Module where

open import CategoryTheory.Operations.Terminal-Type-Module
open import CategoryTheory.Classes.0-Relation-Module
open import CategoryTheory.Classes.0-Category-Module
open import CategoryTheory.Classes.0-Groupoid-Module

data Terminal-Equ-Type
    : 0-Relation-Type Terminal-Type Terminal-Type
  where
    !≡! 
      : Terminal-Equ-Type ! !

instance
  Terminal-Type-0-Relation-Inst : 0-Relation-Class Terminal-Type
  Terminal-Type-0-Relation-Inst = Mk Terminal-Equ-Type

Terminal-0-Relation : 0-Relation-Record
Terminal-0-Relation = Mk Terminal-Type

private 
  0-Id-Equ : {x : Terminal-Type} → (x ⟶ x)
  0-Id-Equ { ! } = !≡!

private
  0-Mul-Equ : {x y z : Terminal-Type} → (x ⟶ y) → (y ⟶ z) → (x ⟶ z)
  0-Mul-Equ { ! } { ! } { ! } !≡! !≡! = !≡!

instance
  Terminal-Type-0-Category-Inst : 0-Category-Class Terminal-Type-0-Relation-Inst
  Terminal-Type-0-Category-Inst = Mk 0-Id-Equ 0-Mul-Equ

Terminal-0-Category : 0-Category-Record
Terminal-0-Category = Mk Terminal-0-Relation

private 
  0-Inv-Equ : {x y : Terminal-Type} → (x ⟶ y) → (y ⟶ x)
  0-Inv-Equ { ! } { ! } !≡! = !≡!

instance
  Terminal-Type-0-Groupoid-Inst : 0-Groupoid-Class Terminal-Type-0-Category-Inst
  Terminal-Type-0-Groupoid-Inst = Mk 0-Inv-Equ

Terminal-0-Groupoid : 0-Groupoid-Record
Terminal-0-Groupoid = Mk Terminal-0-Category
