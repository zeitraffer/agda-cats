{-# OPTIONS --type-in-type --copatterns #-}

module TestRec1 where

Type : Set
Type = Set

record BaseRec : Type where
  constructor Mk
  field fBase : Type

Base : ⦃ base : BaseRec ⦄ → Type
Base ⦃ base ⦄ = BaseRec.fBase base

record FiberRec : Type where
  constructor Mk
  field bBase : BaseRec
  field fFiber : Base → Type

instance
  F→B : ⦃ fiber : FiberRec ⦄ → BaseRec
  F→B ⦃ fiber ⦄ = FiberRec.bBase fiber

Fiber : ⦃ fiber : FiberRec ⦄ → Base → Type
Fiber ⦃ fiber ⦄ = FiberRec.fFiber fiber

---------------------------
-- generic usage

useBase : ⦃ base : BaseRec ⦄ → Type
useBase = Base

useFiber : ⦃ fiber : FiberRec ⦄ → Base → Type
useFiber = Fiber

useFB : ⦃ fiber : FiberRec ⦄ → Type
useFB = Base

---------------------------
-- concrete usage

instance
  iFiber : FiberRec
  iFiber = Mk (Mk Type) (λ type → type → Type)

getBase : Type
getBase = Base

getFiber : Base → Type
getFiber = Fiber
