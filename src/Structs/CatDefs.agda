module Structs.CatDefs where

open import Agda.Primitive public

data MyNat : Set where
  MkZero : MyNat
  MkSucc : MyNat -> MyNat

record CatRec (l : Level) : Set (lsuc l) 
  where
    constructor MkCat
    field
      cOb : Set l
      cMor : (a b : cOb) -> Set l
      cEqu : (a b : cOb) -> (f g : cMor a b) -> Set l
      cId : (a : cOb) -> cMor a a
      cMul : (a b c : cOb) -> cMor a b -> cMor b c -> cMor a c
      -- TODO free graph / algebra structure
open CatRec    

record CatOb {l : Level} 
    (cat : CatRec l) : Set l
  where
    constructor MkOb
    field unOb : cOb cat
open CatOb

record _CatMor_ {l : Level} {cat : CatRec l} 
    (a b : CatOb cat) : Set l
  where
    constructor MkMor
    field unMor : cMor cat (unOb a) (unOb b)
open _CatMor_

record _CatEqu_ {l : Level} {cat : CatRec l} {a b : CatOb cat} 
    (f g : a CatMor b) : Set l
  where
    constructor MkEqu
    field unEqu : cEqu cat (unOb a) (unOb b) (unMor f) (unMor g)
open _CatEqu_

CatId : {l : Level} -> {cat : CatRec l} -> (a : CatOb cat) -> a CatMor a
CatId {l} {cat} a = MkMor (cId cat (unOb a))

_CatMul_ : {l : Level} -> {cat : CatRec l} -> {a b c : CatOb cat} -> 
  a CatMor b -> b CatMor c -> a CatMor c
_CatMul_ {l} {cat} {a} {b} {c} f g = 
  MkMor (cMul cat (unOb a) (unOb b) (unOb c) (unMor f) (unMor g))

-- test compatibility
WrapCat : {l : Level} -> CatRec l -> CatRec l
WrapCat cat = record {
    cOb = CatOb cat;
    cMor = _CatMor_;
    cEqu = \_ _ -> _CatEqu_;
    cId = CatId;
    cMul = \_ _ _ -> _CatMul_
  }

