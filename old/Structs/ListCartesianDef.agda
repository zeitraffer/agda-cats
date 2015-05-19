{-# OPTIONS --type-in-type --copatterns #-}

module Structs.ListCartesianDef where

open import Structs.RelationDef
open import Structs.ListDef
open import Structs.PullbackDef

forwardPullback : 
    {L R B : Type} →
    ⦃ rel : B ↚ B ⦄ →
    {l : B ← L} →
    {r : B ← R} →
    Pullback (mapList l) (mapList r) ← 
    List (Pullback l r)
forwardPullback Nil = MkPullback Nil Nil Nil
forwardPullback (MkPullback xl xr eq ∷ pbs) with forwardPullback pbs
... | MkPullback xls xrs eqs =
  MkPullback (xl ∷ xls) (xr ∷ xrs) (eq ∷ eqs)

backwardPullback : 
    {L R B : Type} →
    ⦃ rel : B ↚ B ⦄ →
    {l : B ← L} →
    {r : B ← R} →
    List (Pullback l r) ← 
    Pullback (mapList l) (mapList r)  
backwardPullback (MkPullback Nil Nil Nil) = Nil
backwardPullback (MkPullback (xl ∷ xls) (xr ∷ xrs) (eq ∷ eqs)) = 
  MkPullback xl xr eq ∷ backwardPullback (MkPullback xls xrs eqs)
backwardPullback (MkPullback (xl ∷ xls) Nil ())
backwardPullback (MkPullback Nil (xr ∷ xrs) ())

forwardReturnPullback : 
    {X Y : Type} →
    ⦃ rel : Y ↚ Y ⦄ →
    ⦃ set : SetoidOfR-Class rel ⦄ →
    (f : Y ← X) →
    Pullback returnList (mapList f) ← X
forwardReturnPullback x = MkPullback (f x) (returnList x) (id (f x) ∷ Nil)

