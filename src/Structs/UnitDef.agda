module Structs.UnitDef where

data Unit : Set where
  ! : Unit

final : {X : Set} → (X → Unit)
final _ = !

