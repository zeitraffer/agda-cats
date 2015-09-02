{-# OPTIONS --type-in-type --copatterns #-}

module TestRec2 where

Type : Set
Type = Set

record BaseRec : Type where
  constructor Mk
  field fType : Type
  field fBase : fType -> Type

Base : {{base : BaseRec}} -> BaseRec.fType base -> Type
Base {{base}} = BaseRec.fBase base

record FiberRec : Type where
  constructor Mk
  field fBase : Type
  field fFiber : fBase → Type

instance
  Fiber:Base : BaseRec
  Fiber:Base = Mk _ FiberRec.fBase

Fiber : ⦃ fiber : FiberRec ⦄ → Base fiber → Type
Fiber ⦃ fiber ⦄ = FiberRec.fFiber fiber

record SectionRec : Type where
  constructor Mk
  field bFiber : FiberRec
  field fSection : (base : Base bFiber) → Fiber base

instance
  Section->Fiber : {{section : SectionRec}} -> FiberRec
  Section->Fiber {{section}} = SectionRec.bFiber section

instance
  Section:Base : BaseRec
  Section:Base = Mk SectionRec (λ section → Base (SectionRec.bFiber section))

Section : ⦃ section : SectionRec ⦄ → (base : Base section) → (Fiber base)
Section ⦃ section ⦄ = SectionRec.fSection section

---------------------------
-- generic usage

useBase : {{base : BaseRec}} -> BaseRec.fType base -> Type
useBase = Base

useFiber : ⦃ fiber : FiberRec ⦄ → Base fiber → Type
useFiber = Fiber

useSection : ⦃ section : SectionRec ⦄ → (base : Base section) → (Fiber base)
useSection = Section

useSection->Fiber : ⦃ section : SectionRec ⦄ → Base section → Type
useSection->Fiber = Fiber

---------------------------
-- concrete usage

Type:Fiber : FiberRec
Type:Fiber = Mk Type (λ type → type → Type)

data Type-Section (type : Type) : (type → Type) where
  MkTS : {value : type} → Type-Section type value

instance
  Type:Section : SectionRec
  Type:Section = Mk Type:Fiber Type-Section

data [] : Type where
  ! : []

[]:Fiber : FiberRec
[]:Fiber = Mk [] (λ u → [])

instance
  []:Section : SectionRec
  []:Section = Mk []:Fiber (λ u → !)

getFiberT : Type → Type
getFiberT = Fiber

getSectionT : (base : Type) → Fiber base
getSectionT = Section

getFiber! : [] → Type
getFiber! = Fiber

getSection! : (base : []) → Fiber base
getSection! = Section
