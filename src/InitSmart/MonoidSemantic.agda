module InitSmart.MonoidSemantic where

open import InitSmart.MonoidModule
open import InitSmart.MonoidNormal

open import Structs.ListDef

------------------------------------
-- helper functions
------------------------------------


------------------------------------
-- semantic functions
------------------------------------
mutual

  -- type mapping
  [_] : 
      {l : Layer} → 
      “ l ” → ‘ l ’
  [ Ob ] = Ob
  [ x ⇒ y ] = ⟦ x ⟧ ⇒ ⟦ y ⟧
  [ f ≡ g ] = ⟦ f ⟧ ≡ ⟦ g ⟧

  -- term mapping
  ⟦_⟧ : 
      {l : Layer} → {t : “ l ”} → 
      « t » → ‹ [ t ] ›

  -- category structure
  ⟦ IdMor ⟧ = mapList returnList
  ⟦ f MulMor g ⟧ = ⟦ f ⟧ mulᴹ ⟦ g ⟧
  ⟦ IdEqu ⟧ = idᴱ
  ⟦ e MulEqu e' ⟧ = ⟦ e ⟧ mulᴱ ⟦ e' ⟧
  ⟦ InvEqu e ⟧ = invᴱ ⟦ e ⟧
  ⟦ e MulMorEqu e' ⟧ = ⟦ e ⟧ mulᴹᴱ ⟦ e' ⟧

  -- monoidal category structure TODO
  ⟦ IdOb ⟧ = 0ᴼ
  ⟦ a MulOb b ⟧ = ⟦ a ⟧ +ᴼ ⟦ b ⟧
  ⟦ f MulObMor g ⟧ = ⟦ f ⟧ +ᴼᴹ ⟦ g ⟧
  ⟦ e MulObEqu e' ⟧ = ⟦ e ⟧ +ᴼᴱ ⟦ e' ⟧
  ⟦ l MulObIdEqu r ⟧ = ⟦ l ⟧ +ᴼidᴱ ⟦ r ⟧
  ⟦ MulObMulEqu f f' g g' ⟧ = +ᴼmulᴱ ⟦ f ⟧ ⟦ f' ⟧ ⟦ g ⟧ ⟦ g' ⟧
  ⟦ NeutrLeftDownMor ⟧ = idᴹ
  ⟦ NeutrLeftUpMor ⟧ = idᴹ
  ⟦ NeutrRightDownMor ⟧ = neutrDᴹ
  ⟦ NeutrRightUpMor ⟧ = neutrUᴹ
  ⟦ AssocLRMor {x} {y} {z} ⟧ = assocLRᴹ {⟦ x ⟧} {⟦ y ⟧} {⟦ z ⟧}
  ⟦ AssocRLMor {x} {y} {z} ⟧ = assocRLᴹ {⟦ x ⟧} {⟦ y ⟧} {⟦ z ⟧}

  -- monoid object structure
  ⟦ ElOb ⟧ = 1ᴼ
  ⟦ IdEl ⟧ = Zᴹ Nilᴹ -- list [0]
  ⟦ MulEl ⟧ = Sᴹ (Sᴹ (Zᴹ Nilᴹ)) -- list [2]
  ⟦ NeutralityLeftEqu ⟧ = idᴱ
  ⟦ NeutralityRightEqu ⟧ = idᴱ
  ⟦ AssociativityEqu ⟧ = idᴱ

{-
  ⟦ NeutrLeftEqu {_} {_} {_} ⟧
  ⟦ NeutrRightEqu {_} {_} {_} ⟧
  ⟦ AssocEqu {_} {_} {_} {_} {_} {_} {_} ⟧

  ⟦ NeutrLeftDownUpIsoEqu {_} ⟧
  ⟦ NeutrLeftUpDownIsoEqu {_} ⟧
  ⟦ NeutrLeftDownMorNatEqu {_} {_} _ ⟧
  ⟦ NeutrLeftUpMorNatEqu {_} {_} _ ⟧
  ⟦ NeutrRightDownUpIsoEqu {_} ⟧
  ⟦ NeutrRightUpDownIsoEqu {_} ⟧
  ⟦ NeutrRightDownMorNatEqu {_} {_} _ ⟧
  ⟦ NeutrRightUpMorNatEqu {_} {_} _ ⟧
  ⟦ AssocLeftIsoEqu {_} {_} {_} ⟧
  ⟦ AssocRightIsoEqu {_} {_} {_} ⟧
  ⟦ AssocLRMorNatEqu {_} {_} {_} {_} {_} {_} _ _ _ ⟧
  ⟦ AssocRLMorNatEqu {_} {_} {_} {_} {_} {_} _ _ _ ⟧
-}
