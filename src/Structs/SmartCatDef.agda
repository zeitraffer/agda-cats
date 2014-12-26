module Structs.SmartCatDef where

open import Agda.Primitive public
open import Structs.LayerDef public

record SmartCatRec (l : Level) : Set (lsuc l) where
  constructor MkSmartRec
  field
    cTag : 
        Layer -> 
        Set l
    cCarrier : 
        {layer : Layer} -> 
        cTag layer -> 
        Set l
    cOb : 
        cTag L2
    cMor : 
        {layer : Layer} ->
        {tag : cTag (LSucc layer)} ->
        (source target : cCarrier tag) ->
        cTag layer
    cId : 
        {layer : Layer} ->
        {tag : cTag (LSucc layer)} ->
        (o : cCarrier tag) ->
        cCarrier (cMor o o)
    cMul : 
        {layer : Layer} ->
        {tag : cTag (LSucc layer)} ->
        {a b c : cCarrier tag} ->
        cCarrier (cMor a b) -> 
        cCarrier (cMor b c) ->
        cCarrier (cMor a c)

