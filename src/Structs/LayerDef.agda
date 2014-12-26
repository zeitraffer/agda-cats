module Structs.LayerDef where

data Layer : Set where
  LZero : Layer
  LSucc : Layer -> Layer

L0 : Layer
L0 = LZero

L1 : Layer
L1 = LSucc L0

L2 : Layer
L2 = LSucc L1

L3 : Layer
L3 = LSucc L2
