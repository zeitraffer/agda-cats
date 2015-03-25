module CategoryTheory.Operations.PropEqualityModule where

open import CategoryTheory.CommonModule

--
-- propositional equality
--

data _=Prop=_ 
    {ℓ : Level} 
    {X : Set ℓ} : 
    (source target : X) → Set ℓ 
  where
    IdProp : (x : X) → x =Prop= x

_MulProp_ : 
    {ℓ : Level} → 
    {X : Set ℓ} → 
    {x y z : X} →
    x =Prop= y →
    y =Prop= z →
    x =Prop= z
(IdProp x) MulProp (IdProp .x) = IdProp x

InvProp : 
    {ℓ : Level} → 
    {X : Set ℓ} → 
    {x y : X} →
    x =Prop= y → 
    y =Prop= x
InvProp (IdProp _) = IdProp _

--
-- extensional equality aka homotopy
--

_=Ext=_ : {ℓ : Level} → {X Y : Set ℓ} → (source target : X → Y) → Set ℓ 
_=Ext=_ {ℓ} {X} {Y} source target = (arg : X) → (source arg =Prop= target arg)

IdExt : 
    {ℓ : Level} → 
    {X Y : Set ℓ} → 
    (f : X → Y) → 
    f =Ext= f
IdExt f x = IdProp (f x)

_MulExt_ : 
    {ℓ : Level} → 
    {X Y : Set ℓ} → 
    {f g h : X → Y} → 
    f =Ext= g →
    g =Ext= h →
    f =Ext= h 
(f=g MulExt g=h) x = (f=g x) MulProp (g=h x)

InvExt : 
    {ℓ : Level} → 
    {X Y : Set ℓ} → 
    {f g : X → Y} → 
    f =Ext= g →
    g =Ext= f 
(InvExt f=g) x = InvProp (f=g x)
