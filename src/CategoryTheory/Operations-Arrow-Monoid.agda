{-# OPTIONS --type-in-type #-}

module CategoryTheory.Operations-Arrow-Monoid where

open import CategoryTheory.Common

module 0-Idᴬ {X : Typeᵀ} where
  data _⇛_ : X ⇸ X where
    ! : {x : X} → x ⇛ x

module 0-Mulᴬ {X Y Z : Typeᵀ} (_⇒₁_ : X ⇸ Y) (_⇒₂_ : Y ⇸ Z) where
  infixr 0 _,_
  data _⇛_ : X ⇸ Z where
    _,_ : {x : X} → {y : Y} → {z : Z} → x ⇒₁ y → y ⇒₂ z → x ⇛ z

open 0-Idᴬ using (!) renaming (_⇛_ to ①ᴬ) public
open 0-Mulᴬ using (_,_) renaming (_⇛_ to _⊗ᴬ_) public
