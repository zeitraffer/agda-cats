{-# OPTIONS --type-in-type --copatterns #-}

module TestRec where

---------------------------
-- synonym for the type of types
Typeᵀ : Set
Typeᵀ = Set

Π : {A : Typeᵀ} → (B : A → Typeᵀ) → Typeᵀ
Π {A} B = (a : A) → B a

id/Type : {A : Typeᵀ} → A → A
id/Type a = a

-- synomym for lambda syntax
infixr -10 id/Type
syntax id/Type (λ a → b) = a ↦ b

---------------------------
-- definitions of type-classes

record Baseᴿ : Typeᵀ where
  constructor Mk
  field fType : Typeᵀ
  field fBase : fType → Typeᵀ

Baseᴹ : ⦃ B : Baseᴿ ⦄ → Baseᴿ.fType B → Typeᵀ
Baseᴹ ⦃ B ⦄ = Baseᴿ.fBase B

record Fiberᴿ : Typeᵀ where
  constructor Mk
  field fBase : Typeᵀ
  field fFiber : fBase → Typeᵀ

instance
  Fiber:Base : Baseᴿ
  Fiber:Base = Mk _ Fiberᴿ.fBase

Fiberᴹ : ⦃ F : Fiberᴿ ⦄ → Baseᴹ F → Typeᵀ
Fiberᴹ ⦃ F ⦄ = Fiberᴿ.fFiber F

record Sectionᴿ : Typeᵀ where
  constructor Mk
  field F : Fiberᴿ
  field fSection : (b : Baseᴹ F) → Fiberᴹ b

instance
  Section->Fiber : ⦃ S : Sectionᴿ ⦄ -> Fiberᴿ
  Section->Fiber ⦃ S ⦄ = Sectionᴿ.F S

instance
  Section:Base : Baseᴿ
  Section:Base = Mk Sectionᴿ (S ↦ Baseᴹ (Sectionᴿ.F S))

Sectionᴹ : ⦃ S : Sectionᴿ ⦄ → (b : Baseᴹ S) → (Fiberᴹ b)
Sectionᴹ ⦃ S ⦄ = Sectionᴿ.fSection S

---------------------------
-- generic usage

useBase : ⦃ B : Baseᴿ ⦄ -> Baseᴿ.fType B -> Typeᵀ
useBase = Baseᴹ

useFiber : ⦃ F : Fiberᴿ ⦄ → Baseᴹ F → Typeᵀ
useFiber = Fiberᴹ

useSection : ⦃ S : Sectionᴿ ⦄ → (b : Baseᴹ S) → (Fiberᴹ b)
useSection = Sectionᴹ

useSection->Fiber : ⦃ S : Sectionᴿ ⦄ → Baseᴹ S → Typeᵀ
useSection->Fiber = Fiberᴹ

---------------------------
-- concrete usage

Type:Fiber : Fiberᴿ
Type:Fiber = Mk Typeᵀ (type ↦ (type → Typeᵀ))

data Type/Section (type : Typeᵀ) : (type → Typeᵀ) where
  MkTS : {value : type} → Type/Section type value

instance
  Type:Section : Sectionᴿ
  Type:Section = Mk Type:Fiber Type/Section

data [] : Typeᵀ where
  ! : []

[]:Fiber : Fiberᴿ
[]:Fiber = Mk [] (u ↦ [])

instance
  []:Section : Sectionᴿ
  []:Section = Mk []:Fiber (u ↦ !)

getFiberT : Typeᵀ → Typeᵀ
getFiberT = Fiberᴹ

getSectionT : (b : Typeᵀ) → Fiberᴹ b
getSectionT = Sectionᴹ

getFiber! : [] → Typeᵀ
getFiber! = Fiberᴹ

getSection! : (b : []) → Fiberᴹ b
getSection! = Sectionᴹ
