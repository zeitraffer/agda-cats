module Structs.Layer2 where

open import Structs.LayerDef public

LOb : Layer
LOb = LZero

LMor : Layer
LMor = LSucc LOb

LEqu : Layer
LEqu = LSucc LMor  
