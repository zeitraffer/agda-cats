module CategoryTheory.Operations.TypeModule where

open import CategoryTheory.CommonModule
open import CategoryTheory.Operations.OperationsModule
open import CategoryTheory.Operations.PropEqualityModule

record _Compose_ 
    {lev : Level}{X Y Z : Set lev}
    (L : X -> Y -> Set lev) (R : Y -> Z -> Set lev) (x : X) (z : Z) : 
    Set lev
  where
    constructor _,_
    field {fY} : Y
    field fLeft : L x fY
    field fRight : R fY z
open _Compose_

--
-- for TypeMap category -- mapping between types
--

record TypeMapType (ℓ : Level) : Set (lsuc ℓ) 
  where
    constructor MkMapType
    field ❪_❫ₜ : Set ℓ
open TypeMapType public

record _←TypeMap-_ {ℓ : Level} (X Y : TypeMapType ℓ) : Set ℓ
  where
    constructor MkMapTypeMor
    field ❪_❫ₜₘ : ❪ X ❫ₜ ← ❪ Y ❫ₜ
open _←TypeMap-_ public

IdMap : {ℓ : Level} (X : TypeMapType ℓ) → (X ←TypeMap- X)
❪ IdMap X ❫ₜₘ = IdFun ❪ X ❫ₜ

_MulMap_ : {ℓ : Level} {X Y Z : TypeMapType ℓ} (f : X ←TypeMap- Y) (g : Y ←TypeMap- Z) → (X ←TypeMap- Z)
❪ f MulMap g ❫ₜₘ = ❪ f ❫ₜₘ MulFun ❪ g ❫ₜₘ

record _=TypeMap=_ {ℓ : Level} {X Y : TypeMapType ℓ} (f g : X ←TypeMap- Y) : Set ℓ
  where
    constructor MkMapTypeEqu
    field ❪_❫ₜₑ : ❪ f ❫ₜₘ =Ext= ❪ g ❫ₜₘ
open _=TypeMap=_ public

IdMapEqu : {ℓ : Level} {X Y : TypeMapType ℓ} (f : X ←TypeMap- Y) → (f =TypeMap= f)
❪ IdMapEqu f ❫ₜₑ = IdExt ❪ f ❫ₜₘ

_MulMapEqu_ : {ℓ : Level} {X Y : TypeMapType ℓ} {f g h : X ←TypeMap- Y} 
    (f=g : f =TypeMap= g) (g=h : g =TypeMap= h) → (f =TypeMap= h)
❪ f=g MulMapEqu g=h ❫ₜₑ = ❪ f=g ❫ₜₑ MulExt ❪ g=h ❫ₜₑ

-- MulTypeMorEqu
-- TODO neutrality, associativity

--
-- for TypeRel category -- relations between types
--

record TypeRelType (ℓ : Level) : Set (lsuc ℓ) 
  where
    constructor MkRelType
    field ❪_❫ᵣ : Set ℓ
open TypeRelType public

record _←TypeRel-_ {ℓ : Level} (X Y : TypeRelType ℓ) : Set (lsuc ℓ)
  where
    constructor MkRelTypeMor
    field ❪_❫ᵣₘ : ❪ X ❫ᵣ → ❪ Y ❫ᵣ → Set ℓ
open _←TypeRel-_ public

IdRel : {ℓ : Level} (X : TypeRelType ℓ) → (X ←TypeRel- X)
❪ IdRel X ❫ᵣₘ = _=Prop=_

_MulRel_ : {ℓ : Level} {X Y Z : TypeRelType ℓ} (f : X ←TypeRel- Y) (g : Y ←TypeRel- Z) → (X ←TypeRel- Z)
❪ f MulRel g ❫ᵣₘ = ❪ f ❫ᵣₘ Compose ❪ g ❫ᵣₘ
