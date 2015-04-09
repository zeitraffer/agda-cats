module InitSmart.MonoidNormal where

open import Structs.Layer2
open import Structs.UnitDef
open import Structs.ListDef

mutual

  data ‘_’ : Layer → Set where
    Ob : ‘ LOb ’
    _⇒_ : {ob : ‘ LOb ’} → (x y : ‹ ob ›) → ‘ LMor ’
    _≡_ : {mor : ‘ LMor ’} → (f g : ‹ mor ›) → ‘ LEqu ’

  data ‹_› : {layer : Layer} → ‘ layer ’ → Set where
    MkO : List Unit → ‹ Ob ›
    MkM : (ll : List (List Unit)) → ‹ MkO (flattenList ll) ⇒ MkO (mapList final ll) › 
    MkE : {mor : ‘ LMor ’} → {m m' : ‹ mor ›} → ‹ m ≡ m' › -- XXX fake

