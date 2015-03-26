module Structs.RelModule where

open import Structs.NaturalModule public

record RelationLevel
    {ℓ² : Level} 
    (ob² : Type ℓ²) 
    {ℓ¹ : Level} 
    (ob¹ : Type ℓ¹) : 
    Type ZeroLev
  where
    constructor MkLevel
    field
      unLevel : Level
open RelationLevel public

record RelationType 
    (ℓᴬ : Level) 
    {ℓ² : Level} 
    (ob² : Type ℓ²) 
    {ℓ¹ : Level} 
    (ob¹ : Type ℓ¹) : 
    Type (ℓ¹ ⊔ ℓ² ⊔ SuccLev ℓᴬ)
  where
    constructor MkRelation
    field
      unRelation : ob² → ob¹ → Type ℓᴬ
open RelationType public

_←❪_❫-_ : 
    {ℓ¹ ℓ² ℓᴬ : Level} {ob² : Type ℓ²} {ob¹ : Type ℓ¹} → 
    ob² → RelationType ℓᴬ ob² ob¹ → ob¹ → Type ℓᴬ
o₂ ←❪ r ❫- o₁ = unRelation r o₂ o₁

_←_ : 
    {ℓ¹ ℓ² : Level} {ob² : Type ℓ²} {ob¹ : Type ℓ¹} 
    {{l : RelationLevel ob² ob¹}} {{q : RelationType (unLevel l) ob² ob¹}} → 
    ob²  → ob¹ → Type (unLevel l)
_←_ {{q = q}} o₂ o₁ = unRelation q o₂ o₁

LiftRelation : 
    {ℓ¹ ℓ² ℓᴬ : Level} {ob² : Type ℓ²} {ob¹ : Type ℓ¹} 
    (ℓᴬ⁺ : Level) →
    RelationType ℓᴬ ob² ob¹ → RelationType (ℓᴬ ⊔ ℓᴬ⁺) ob² ob¹
unRelation (LiftRelation ℓᴬ⁺ r) o₂ o₁ = LiftType ℓᴬ⁺ (unRelation r o₂ o₁)

instance
  TypeMapLevel : {ℓ¹ ℓ² : Level} → RelationLevel (Type ℓ²) (Type ℓ¹)
  unLevel (TypeMapLevel {ℓ¹} {ℓ²}) = ℓ¹ ⊔ ℓ²
  TypeMapRelation : {ℓ¹ ℓ² : Level} → RelationType (ℓ¹ ⊔ ℓ²) (Type ℓ²) (Type ℓ¹)
  unRelation TypeMapRelation o₂ o₁ = o₁ → o₂

record _←Relation-_ 
    {ℓ¹ ℓ² ℓᴬ¹ ℓᴬ² : Level} 
    {ob² : Type ℓ²} {ob¹ : Type ℓ¹} 
    (r² : RelationType ℓᴬ² ob² ob¹) (r¹ : RelationType ℓᴬ¹ ob² ob¹) : 
    Type (ℓ¹ ⊔ ℓ² ⊔ ℓᴬ¹ ⊔ ℓᴬ²)
  where
    constructor MkRelationMor
    field
      unQuiverMor : 
        (o² : ob²) → (o¹ : ob¹) → 
          (o² ←❪ r² ❫- o¹) ← (o² ←❪ r¹ ❫- o¹)
open _←Relation-_ public

--
-- morphisms between relations
--
instance
  RelMapLevel : 
      {ℓ¹ ℓ² ℓᴬ¹ ℓᴬ² : Level} {ob² : Type ℓ²} {ob¹ : Type ℓ¹} → 
      RelationLevel (RelationType ℓᴬ² ob² ob¹) (RelationType ℓᴬ¹ ob² ob¹)
  unLevel (RelMapLevel {ℓ¹} {ℓ²} {ℓᴬ¹} {ℓᴬ²}) = ℓ¹ ⊔ ℓ² ⊔ ℓᴬ¹ ⊔ ℓᴬ²
  RelMapRelation : 
      {ℓ¹ ℓ² ℓᴬ¹ ℓᴬ² : Level} {ob² : Type ℓ²} {ob¹ : Type ℓ¹} → 
      RelationType (ℓ¹ ⊔ ℓ² ⊔ ℓᴬ¹ ⊔ ℓᴬ²) (RelationType ℓᴬ² ob² ob¹) (RelationType ℓᴬ¹ ob² ob¹)
  unRelation RelMapRelation r₂ r₁ = r₂ ←Relation- r₁

data EquType 
    {ℓ : Level} 
    (ob : Type ℓ) : 
    ob → ob → Type ℓ
  where
    𝟙 : 
      (o : ob) → EquType ob o o

IdRel : 
    {ℓ : Level} (ob : Type ℓ) → 
    RelationType ℓ ob ob
unRelation (IdRel ob) = EquType ob

data CompType 
    {ℓ¹ ℓ² ℓ³ ℓᴬ³² ℓᴬ²¹ : Level} {ob¹ : Type ℓ¹} {ob² : Type ℓ²} {ob³ : Type ℓ³}
    (r³² : RelationType ℓᴬ³² ob³ ob²) (r²¹ : RelationType ℓᴬ²¹ ob² ob¹) : 
    ob³ → ob¹ → Type (ℓ¹ ⊔ ℓ² ⊔ ℓ³ ⊔ ℓᴬ³² ⊔ ℓᴬ²¹)
  where
    _,_ : 
      {o¹ : ob¹} {o² : ob²} {o³ : ob³} → 
      (o³ ←❪ r³² ❫- o²) → (o² ←❪ r²¹ ❫- o¹) → 
        CompType r³² r²¹ o³ o¹

_MulRel_ : 
    {ℓ¹ ℓ² ℓ³ ℓᴬ³² ℓᴬ²¹ : Level} {ob¹ : Type ℓ¹} {ob² : Type ℓ²} {ob³ : Type ℓ³}
    (r³² : RelationType ℓᴬ³² ob³ ob²) (r²¹ : RelationType ℓᴬ²¹ ob² ob¹) →
    RelationType (ℓ¹ ⊔ ℓ² ⊔ ℓ³ ⊔ ℓᴬ³² ⊔ ℓᴬ²¹) ob³ ob¹
unRelation (r³² MulRel r²¹) = CompType r³² r²¹

powerRel : 
    NaturalType → {ℓ ℓᴬ : Level} {ob : Type ℓ} → 
    RelationType ℓᴬ ob ob → RelationType (ℓ ⊔ ℓᴬ) ob ob
powerRel ZeroNat {ℓ} {ℓᴬ} {ob} _ = LiftRelation ℓᴬ (IdRel ob)
powerRel (SuccNat ZeroNat) {ℓ} r = LiftRelation ℓ r
powerRel (SuccNat (SuccNat n)) r = r MulRel (powerRel (SuccNat n) r)
