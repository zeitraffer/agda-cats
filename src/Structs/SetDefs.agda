module Structs.SetDefs where

open import Agda.Primitive public

record SetRec (l : Level) : Set (lsuc l) 
  where
    constructor MkSet
    field
      sOb : Set l
      sMor : (a b : sOb) -> Set l
      sId : (a : sOb) -> sMor a a
      sMul : (a b c : sOb) -> sMor a b -> sMor b c -> sMor a c
      sInv : (a b : sOb) -> sMor a b -> sMor b a
open SetRec    

record SetOb {l : Level} 
    (set : SetRec l) : Set l
  where
    constructor MkOb
    field unOb : sOb set
open SetOb

record _SetMor_ {l : Level} {set : SetRec l} 
    (a b : SetOb set) : Set l
  where
    constructor MkMor
    field unMor : sMor set (unOb a) (unOb b)
open _SetMor_


