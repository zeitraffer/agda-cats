{-# OPTIONS --type-in-type --copatterns #-}

module Structs.LayerDef where

data Layer : Set where
  LZero : Layer
  LSucc_ : Layer → Layer
