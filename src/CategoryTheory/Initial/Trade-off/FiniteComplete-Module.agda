{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Initial.Trade-off.FiniteComplete-Module where

------------------------------------------
-- `Layer` - level in categorical syntax
-- 

data Layer 
    : Set 
  where
    LZero 
      : Layer
    LSucc 
      : Layer → Layer

Ob : Layer
Ob = LZero

Mor : Layer
Mor = LSucc Ob

Equ : Layer
Equ = LSucc Mor  

--------------------------------
-- `_↠_` - styles of morphisms
-- 

data _↠_
    : (arg res : Layer) → Set 
  where
    ⇒ 
      : Ob ↠ Mor
    ⇔ 
      : Ob ↠ Mor
    ≡ 
      : Mor ↠ Equ

------------------------------------------
mutual

  infix 1 _⊗_ _∙_∙_
  infixl 10 _MulMor_ _MulEqu_ _MulMorEqu_ 
  infixl 10 _MkPairOb_ _MkPairMor_ _MkPairMEqu_ _MkPairIEqu_ 

  ---------------------------------------
  -- internal 'types' of terms
  ---------------------------------------
  data “_” 
      : Layer 
      → Set 
    where

      -- type of objects of the specified category
      ⋆ 

        --------
        : “ Ob ”

      -- type of objects of terminal category
      ① 

        --------
        : “ Ob ”

      -- type of pairs of objects
      _⊗_ 

        : “ Ob ”
        → “ Ob ”
        ---------
        → “ Ob ”

      -- creates a morphism type of a given style from two objects
      _∙_∙_ 

        : {layer-ob layer-mor : Layer} 
        → {ob : “ layer-ob ”} 
        → « ob » 
        → layer-ob ↠ layer-mor
        → « ob » 
        ---------------
        → “ layer-mor ”

      -- type of commutative squares
      Square

        : {ob : “ Ob ”} 
        → {⟹ₕ : Ob ↠ Mor }
        → {⟹ᵥ : Ob ↠ Mor }
        → {x11 x12 x21 x22 : « ob »}
        → « x11 ∙ ⟹ₕ ∙ x12 »
        → « x21 ∙ ⟹ₕ ∙ x22 »
        → « x11 ∙ ⟹ᵥ ∙ x21 »
        → « x12 ∙ ⟹ᵥ ∙ x22 »
        ----------------------
        → “ Equ ”


  ---------------------------------------
  -- terms of internal 'types'
  ---------------------------------------
  data «_» 
      : {layer : Layer} 
      → “ layer ” 
      → Set 
    where

    --=============================================
    -- category structure
    --=============================================

      IdMor 
        : {ob : “ Ob ”} 
        → (x : « ob »)
        → « x ∙ ⇒ ∙ x »

      IdIso 
        : {ob : “ Ob ”} 
        → (x : « ob »)
        → « x ∙ ⇔ ∙ x »

      _MulMor_ 
        : {ob : “ Ob ”} 
        → {x y z : « ob »} 
        → « x ∙ ⇒ ∙ y »
        → « y ∙ ⇒ ∙ z »
        → « x ∙ ⇒ ∙ z »

      _MulIso_ 
        : {ob : “ Ob ”} 
        → {x y z : « ob »} 
        → « x ∙ ⇔ ∙ y »
        → « y ∙ ⇔ ∙ z »
        → « x ∙ ⇔ ∙ z »

      IdEqu 
        : {mor : “ Mor ”} 
        → (f : « mor »)
        → « f ∙ ≡ ∙ f »

      _MulEqu_ 
        : {mor : “ Mor ”} 
        → {f g h : « mor »} 
        → « f ∙ ≡ ∙ g »
        → « g ∙ ≡ ∙ h »
        → « f ∙ ≡ ∙ h »

      InvEqu 
        : {mor : “ Mor ”} 
        → {f g : « mor »} 
        → « f ∙ ≡ ∙ g »
        → « g ∙ ≡ ∙ f »

      _MulMorEqu_
        : {ob : “ Ob ”}
        → {x y z : « ob »} 
        → {f f' : « x ∙ ⇒ ∙ y »} 
        → {g g' : « y ∙ ⇒ ∙ z »} 
        → « f ∙ ≡ ∙ f' »
        → « g ∙ ≡ ∙ g' »
        → « f MulMor g ∙ ≡ ∙ f' MulMor g' »

      _MulIsoEqu_
        : {ob : “ Ob ”}
        → {x y z : « ob »} 
        → {f f' : « x ∙ ⇔ ∙ y »} 
        → {g g' : « y ∙ ⇔ ∙ z »} 
        → « f ∙ ≡ ∙ f' »
        → « g ∙ ≡ ∙ g' »
        → « f MulIso g ∙ ≡ ∙ f' MulIso g' »

      MorNeutrLeftEqu
        : {ob : “ Ob ”}
        → {x y : « ob »} 
        → (f : « x ∙ ⇒ ∙ y »)
        → « IdMor x MulMor f ∙ ≡ ∙ f »

      MorNeutrRightEqu
        : {ob : “ Ob ”}
        → {x y : « ob »} 
        → (f : « x ∙ ⇒ ∙ y »)
        → « f MulMor IdMor y ∙ ≡ ∙ f »

      IsoNeutrLeftEqu
        : {ob : “ Ob ”}
        → {x y : « ob »} 
        → (f : « x ∙ ⇔ ∙ y »)
        → « IdIso x MulIso f ∙ ≡ ∙ f »

      IsoNeutrRightEqu
        : {ob : “ Ob ”}
        → {x y : « ob »} 
        → (f : « x ∙ ⇔ ∙ y »)
        → « f MulIso IdIso y ∙ ≡ ∙ f »

      MorAssocEqu
        : {ob : “ Ob ”}
        → {x y z t : « ob »} 
        → (f : « x ∙ ⇒ ∙ y ») 
        → (g : « y ∙ ⇒ ∙ z ») 
        → (h : « z ∙ ⇒ ∙ t ») 
        → « (f MulMor g) MulMor h ∙ ≡ ∙ f MulMor (g MulMor h) »

      IsoAssocEqu
        : {ob : “ Ob ”}
        → {x y z t : « ob »} 
        → (f : « x ∙ ⇔ ∙ y ») 
        → (g : « y ∙ ⇔ ∙ z ») 
        → (h : « z ∙ ⇔ ∙ t ») 
        → « (f MulIso g) MulIso h ∙ ≡ ∙ f MulIso (g MulIso h) »

    --=============================================
    -- isomorphisms
    --=============================================

      -- an isomorphism consists of a pair of morphisms endowed by a pair of equations
      MkIso
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → {forward : « x ∙ ⇒ ∙ y »}
        → {backward : « y ∙ ⇒ ∙ x »}
        → « forward MulMor backward ∙ ≡ ∙ IdMor x »
        → « IdMor y ∙ ≡ ∙ backward MulMor forward »
        → « x ∙ ⇔ ∙ y »

      -- forward component of isomorphism
      IsoForwardMor
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → « x ∙ ⇔ ∙ y »
        → « x ∙ ⇒ ∙ y »

      -- backward component of isomorphism
      IsoBackwardMor
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → « x ∙ ⇔ ∙ y »
        → « y ∙ ⇒ ∙ x »

      -- equation of isomorphism at the begin object
      IsoBeginEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → (i : « x ∙ ⇔ ∙ y »)
        → « (IsoForwardMor i) MulMor (IsoBackwardMor i) ∙ ≡ ∙ IdMor x »

      -- equation of isomorphism at the end object
      IsoEndEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → (i : « x ∙ ⇔ ∙ y »)
        → « IdMor y ∙ ≡ ∙ (IsoBackwardMor i) MulMor (IsoForwardMor i) »

      -- decompose and than compose isomorphism 
      MkIsoCorrectEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → (i : « x ∙ ⇔ ∙ y »)
        → « i ∙ ≡ ∙ MkIso (IsoBeginEqu i) (IsoEndEqu i) »

      -- compose and decompose isomorphism, at forward
      IsoForwardMorCorrectEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → {forward : « x ∙ ⇒ ∙ y »}
        → {backward : « y ∙ ⇒ ∙ x »}
        → (ex : « forward MulMor backward ∙ ≡ ∙ IdMor x »)
        → (ey : « IdMor y ∙ ≡ ∙ backward MulMor forward »)
        → « IsoForwardMor (MkIso ex ey) ∙ ≡ ∙ forward »

      -- compose and decompose isomorphism, at backward
      IsoBackwardMorCorrectEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → {forward : « x ∙ ⇒ ∙ y »}
        → {backward : « y ∙ ⇒ ∙ x »}
        → (ex : « forward MulMor backward ∙ ≡ ∙ IdMor x »)
        → (ey : « IdMor y ∙ ≡ ∙ backward MulMor forward »)
        → « IsoBackwardMor (MkIso ex ey) ∙ ≡ ∙ backward »

      -- morphism constructor acts on equalities
      MkIsoEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → {forward forward' : « x ∙ ⇒ ∙ y »}
        → {backward backward' : « y ∙ ⇒ ∙ x »}
        → {ex : « forward MulMor backward ∙ ≡ ∙ IdMor x »}
        → {ey : « IdMor y ∙ ≡ ∙ backward MulMor forward »}
        → {ex' : « forward' MulMor backward' ∙ ≡ ∙ IdMor x »}
        → {ey' : « IdMor y ∙ ≡ ∙ backward' MulMor forward' »}
        → (eforw : « forward ∙ ≡ ∙ forward' »)
        → (eback : « backward ∙ ≡ ∙ backward' »)
        → « MkIso ex ey ∙ ≡ ∙ MkIso ex' ey' »

      -- forward projection acts on equalities
      IsoForwardMorEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → {i i' : « x ∙ ⇔ ∙ y »}
        → « i ∙ ≡ ∙ i' »
        → « IsoForwardMor i ∙ ≡ ∙ IsoForwardMor i' »

      -- backward projection acts on equalities
      IsoBackwardMorEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → {i i' : « x ∙ ⇔ ∙ y »}
        → « i ∙ ≡ ∙ i' »
        → « IsoBackwardMor i ∙ ≡ ∙ IsoBackwardMor i' »

      InvIso
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → « x ∙ ⇔ ∙ y »
        → « y ∙ ⇔ ∙ x »

      InvIsoEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → {i i' : « x ∙ ⇔ ∙ y »}
        → « i ∙ ≡ ∙ i' »
        → « InvIso i ∙ ≡ ∙ InvIso i' »

      InvDefEqu
        : {ob : “ Ob ”} 
        → {x y : « ob »} 
        → (i : « x ∙ ⇔ ∙ y »)
        → « InvIso i ∙ ≡ ∙ MkIso (InvEqu (IsoEndEqu i)) (InvEqu (IsoBeginEqu i)) »

      IdIsoForwardEqu
        : {ob : “ Ob ”} 
        → {x : « ob »} 
        → « IsoForwardMor (IdIso x) ∙ ≡ ∙ IdMor x »

      IdIsoBackwardEqu
        : {ob : “ Ob ”} 
        → {x : « ob »} 
        → « IsoBackwardMor (IdIso x) ∙ ≡ ∙ IdMor x »

      MulIsoForwardEqu
        : {ob : “ Ob ”} 
        → {x y z : « ob »} 
        → {ixy : « x ∙ ⇔ ∙ y »}
        → {iyz : « y ∙ ⇔ ∙ z »}
        → « IsoForwardMor (ixy MulIso iyz) ∙ ≡ ∙ 
            (IsoForwardMor ixy) MulMor (IsoForwardMor iyz) »

      MulIsoBackwardEqu
        : {ob : “ Ob ”} 
        → {x y z : « ob »} 
        → {ixy : « x ∙ ⇔ ∙ y »}
        → {iyz : « y ∙ ⇔ ∙ z »}
        → « IsoBackwardMor (ixy MulIso iyz) ∙ ≡ ∙ 
            (IsoBackwardMor iyz) MulMor (IsoBackwardMor ixy) »

    --=============================================
    -- commutative squares
    --=============================================

      -- make square as equation
      MkSquareMorMor

        : {ob : “ Ob ”} 
        → {x11 x12 x21 x22 : « ob »}
        → {f1x : « x11 ∙ ⇒ ∙ x12 »}
        → {f2x : « x21 ∙ ⇒ ∙ x22 »}
        → {fx1 : « x11 ∙ ⇒ ∙ x21 »}
        → {fx2 : « x12 ∙ ⇒ ∙ x22 »}
        → « f1x MulMor fx2 ∙ ≡ ∙ fx1 MulMor f2x »
        ---------------------------------
        → « Square f1x f2x fx1 fx2 »

      -- extract equation from square
      SquareMorMorEqu

        : {≡ : Mor ↠ Equ}
        → {ob : “ Ob ”} 
        → {x11 x12 x21 x22 : « ob »}
        → {f1x : « x11 ∙ ⇒ ∙ x12 »}
        → {f2x : « x21 ∙ ⇒ ∙ x22 »}
        → {fx1 : « x11 ∙ ⇒ ∙ x21 »}
        → {fx2 : « x12 ∙ ⇒ ∙ x22 »}
        → « Square f1x f2x fx1 fx2 »
        ---------------------------------
        → « f1x MulMor fx2 ∙ ≡ ∙ fx1 MulMor f2x »

      -- TODO Square for Iso

    --=============================================
    -- the terminal category structure
    --=============================================

      MkOneOb
        : « ① »

      OneCorrectIso
        : (x : « ① »)
        → « MkOneOb ∙ ⇔ ∙ x »

      OneCorrectIsoNatEqu
        : {x y : « ① »}
        → (f : « x ∙ ⇒ ∙ y »)
        → « Square 
            (IdMor MkOneOb) f 
            (OneCorrectIso x) (OneCorrectIso y) »

      OneOkEqu      
        : « OneCorrectIso MkOneOb ∙ ≡ ∙ IdIso MkOneOb »

    --=============================================
    -- the terminal category structure
    --=============================================

      TerminalOb
        : « ① »
        → « ⋆ »

      TerminalMor
        : {x y : « ① »}
        → « x ∙ ⇒ ∙ y »
        → « TerminalOb x ∙ ⇒ ∙ TerminalOb y »

      TerminalIso
        : {x y : « ① »}
        → « x ∙ ⇔ ∙ y »
        → « TerminalOb x ∙ ⇔ ∙ TerminalOb y »

      TerminalMEqu
        : {x y : « ① »}
        → {f g : « x ∙ ⇒ ∙ y »}
        → « f ∙ ≡ ∙ g »
        → « TerminalMor f ∙ ≡ ∙ TerminalMor g »

      TerminalIEqu
        : {x y : « ① »}
        → {f g : « x ∙ ⇔ ∙ y »}
        → « f ∙ ≡ ∙ g »
        → « TerminalIso f ∙ ≡ ∙ TerminalIso g »

      TerminalUnitMor
        : (x : « ⋆ »)
        → « x ∙ ⇒ ∙ TerminalOb MkOneOb »

      TerminalUnitMorNatMEqu
        : {x y : « ⋆ »}
        → (f : « x ∙ ⇔ ∙ y »)
        → « Square
            f (TerminalMor (IdMor MkOneOb)) 
            (TerminalUnitMor x) (TerminalUnitMor y) »

    --=============================================
    -- product of categories structure
    --=============================================

      _MkPairOb_ 
        : {obl obr : “ Ob ”}
        → « obl »
        → « obr »
        → « obl ⊗ obr »

      _MkPairMor_
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → « l ∙ ⇒ ∙ l' »
        → « r ∙ ⇒ ∙ r' »
        → « l MkPairOb r ∙ ⇒ ∙ l' MkPairOb r' »

      _MkPairIso_
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → « l ∙ ⇔ ∙ l' »
        → « r ∙ ⇔ ∙ r' »
        → « l MkPairOb r ∙ ⇔ ∙ l' MkPairOb r' »

      _MkPairMEqu_
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → {fl fl' : « l ∙ ⇒ ∙ l' »}
        → {fr fr' : « r ∙ ⇒ ∙ r' »}
        → « fl ∙ ≡ ∙ fl' »
        → « fr ∙ ≡ ∙ fr' »
        → « fl MkPairMor fr ∙ ≡ ∙ fl' MkPairMor fr' »

      _MkPairIEqu_
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → {fl fl' : « l ∙ ⇔ ∙ l' »}
        → {fr fr' : « r ∙ ⇔ ∙ r' »}
        → « fl ∙ ≡ ∙ fl' »
        → « fr ∙ ≡ ∙ fr' »
        → « fl MkPairIso fr ∙ ≡ ∙ fl' MkPairIso fr' »

      PairLeftOb
        : {obl obr : “ Ob ”}
        → « obl ⊗ obr »
        → « obl »

      PairRightOb
        : {obl obr : “ Ob ”}
        → « obl ⊗ obr »
        → « obr »

      PairLeftMor
        : {obl obr : “ Ob ”}
        → {p q : « obl ⊗ obr »}
        → « p ∙ ⇒ ∙ q »
        → « PairLeftOb p ∙ ⇒ ∙ PairLeftOb q »

      PairLeftIso
        : {obl obr : “ Ob ”}
        → {p q : « obl ⊗ obr »}
        → « p ∙ ⇔ ∙ q »
        → « PairLeftOb p ∙ ⇔ ∙ PairLeftOb q »

      PairRightMor
        : {obl obr : “ Ob ”}
        → {p q : « obl ⊗ obr »}
        → « p ∙ ⇒ ∙ q »
        → « PairRightOb p ∙ ⇒ ∙ PairRightOb q »

      PairRightIso
        : {obl obr : “ Ob ”}
        → {p q : « obl ⊗ obr »}
        → « p ∙ ⇔ ∙ q »
        → « PairRightOb p ∙ ⇔ ∙ PairRightOb q »

      PairLeftMEqu
        : {obl obr : “ Ob ”}
        → {p q : « obl ⊗ obr »}
        → {f g : « p ∙ ⇒ ∙ q »}
        → « f ∙ ≡ ∙ g »
        → « PairLeftMor f ∙ ≡ ∙ PairLeftMor g »

      PairLeftIEqu
        : {obl obr : “ Ob ”}
        → {p q : « obl ⊗ obr »}
        → {f g : « p ∙ ⇔ ∙ q »}
        → « f ∙ ≡ ∙ g »
        → « PairLeftIso f ∙ ≡ ∙ PairLeftIso g »

      PairRightMEqu
        : {obl obr : “ Ob ”}
        → {p q : « obl ⊗ obr »}
        → {f g : « p ∙ ⇒ ∙ q »}
        → « f ∙ ≡ ∙ g »
        → « PairRightMor f ∙ ≡ ∙ PairRightMor g »

      PairRightIEqu
        : {obl obr : “ Ob ”}
        → {p q : « obl ⊗ obr »}
        → {f g : « p ∙ ⇔ ∙ q »}
        → « f ∙ ≡ ∙ g »
        → « PairRightIso f ∙ ≡ ∙ PairRightIso g »

      _MkPairIdEqu_
        : {obl obr : “ Ob ”}
        → (l : « obl »)
        → (r : « obr »)
        → « IdMor l MkPairMor IdMor r ∙ ≡ ∙ IdMor (l MkPairOb r) »

      MkPairMorEqu
        : {obl obr : “ Ob ”}
        → {al bl cl : « obl »}
        → {ar br cr : « obr »}
        → (fl : « al ∙ ⇒ ∙ bl »)
        → (gl : « bl ∙ ⇒ ∙ cl »)
        → (fr : « ar ∙ ⇒ ∙ br »)
        → (gr : « br ∙ ⇒ ∙ cr »)
        → « (fl MulMor gl) MkPairMor (fr MulMor gr) ∙ ≡ ∙ 
            (fl MkPairMor fr) MulMor (gl MkPairMor gr) »

      MkPairIsoEqu
        : {obl obr : “ Ob ”}
        → {al bl cl : « obl »}
        → {ar br cr : « obr »}
        → (fl : « al ∙ ⇔ ∙ bl »)
        → (gl : « bl ∙ ⇔ ∙ cl »)
        → (fr : « ar ∙ ⇔ ∙ br »)
        → (gr : « br ∙ ⇔ ∙ cr »)
        → « (fl MulIso gl) MkPairIso (fr MulIso gr) ∙ ≡ ∙ 
            (fl MkPairIso fr) MulIso (gl MkPairIso gr) »

      PairLeftIdMEqu
        : {obl obr : “ Ob ”}
        → (p : « obl ⊗ obr »)
        → « PairLeftMor (IdMor p) ∙ ≡ ∙ IdMor (PairLeftOb p) »

      PairLeftIdIEqu
        : {obl obr : “ Ob ”}
        → (p : « obl ⊗ obr »)
        → « PairLeftIso (IdIso p) ∙ ≡ ∙ IdIso (PairLeftOb p) »

      PairRightIdMEqu
        : {obl obr : “ Ob ”}
        → (p : « obl ⊗ obr »)
        → « PairRightMor (IdMor p) ∙ ≡ ∙ IdMor (PairRightOb p) »

      PairRightIdIEqu
        : {obl obr : “ Ob ”}
        → (p : « obl ⊗ obr »)
        → « PairRightIso (IdIso p) ∙ ≡ ∙ IdIso (PairRightOb p) »

      _PairLeftMulMEqu_
        : {obl obr : “ Ob ”}
        → {p q r : « obl ⊗ obr »}
        → (f : « p ∙ ⇒ ∙ q »)
        → (g : « q ∙ ⇒ ∙ r »)
        → « PairLeftMor (f MulMor g) ∙ ≡ ∙ PairLeftMor f MulMor PairLeftMor g »

      _PairLeftMulIEqu_
        : {obl obr : “ Ob ”}
        → {p q r : « obl ⊗ obr »}
        → (f : « p ∙ ⇔ ∙ q »)
        → (g : « q ∙ ⇔ ∙ r »)
        → « PairLeftIso (f MulIso g) ∙ ≡ ∙ PairLeftIso f MulIso PairLeftIso g »

      _PairRightMulMEqu_
        : {obl obr : “ Ob ”}
        → {p q r : « obl ⊗ obr »}
        → (f : « p ∙ ⇒ ∙ q »)
        → (g : « q ∙ ⇒ ∙ r »)
        → « PairRightMor (f MulMor g) ∙ ≡ ∙ PairRightMor f MulMor PairRightMor g »

      _PairRightMulIEqu_
        : {obl obr : “ Ob ”}
        → {p q r : « obl ⊗ obr »}
        → (f : « p ∙ ⇔ ∙ q »)
        → (g : « q ∙ ⇔ ∙ r »)
        → « PairRightIso (f MulIso g) ∙ ≡ ∙ PairRightIso f MulIso PairRightIso g »

      MkPairCorrectIso
        : {obl obr : “ Ob ”}
        → (p : « obl ⊗ obr »)
        → « PairLeftOb p MkPairOb PairRightOb p ∙ ⇔ ∙ p »

      _PairLeftCorrectIso_
        : {obl obr : “ Ob ”}
        → (l : « obl »)
        → (r : « obr »)
        → « PairLeftOb (l MkPairOb r) ∙ ⇔ ∙ l »

      _PairRightCorrectIso_
        : {obl obr : “ Ob ”}
        → (l : « obl »)
        → (r : « obr »)
        → « PairRightOb (l MkPairOb r) ∙ ⇔ ∙ r »

      MkPairCorrectIsoNatMEqu
        : {obl obr : “ Ob ”}
        → {p q : « obl ⊗ obr »}
        → (f : « p ∙ ⇒ ∙ q »)
        → « Square
            (PairLeftMor f MkPairMor PairRightMor f) f
            (MkPairCorrectIso p) (MkPairCorrectIso q) »

      MkPairCorrectIsoNatIEqu
        : {obl obr : “ Ob ”}
        → {p q : « obl ⊗ obr »}
        → (f : « p ∙ ⇔ ∙ q »)
        → « Square
            (PairLeftIso f MkPairIso PairRightIso f) f
            (MkPairCorrectIso p) (MkPairCorrectIso q) »

      _PairLeftCorrectIsoNatMEqu_
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → (fl : « l ∙ ⇒ ∙ l' »)
        → (fr : « r ∙ ⇒ ∙ r' »)
        → « Square
            (PairLeftMor (fl MkPairMor fr)) fl
            (l PairLeftCorrectIso r) (l' PairLeftCorrectIso r') »

      _PairLeftCorrectIsoNatIEqu_
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → (fl : « l ∙ ⇔ ∙ l' »)
        → (fr : « r ∙ ⇔ ∙ r' »)
        → « Square
            (PairLeftIso (fl MkPairIso fr)) fl
            (l PairLeftCorrectIso r) (l' PairLeftCorrectIso r') »

      _PairRightCorrectIsoNatMEqu_
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → (fl : « l ∙ ⇒ ∙ l' »)
        → (fr : « r ∙ ⇒ ∙ r' »)
        → « Square 
            (PairRightMor (fl MkPairMor fr)) fr
            (l PairRightCorrectIso r) (l' PairRightCorrectIso r') »

      _PairRightCorrectIsoNatIEqu_
        : {obl obr : “ Ob ”}
        → {l l' : « obl »}
        → {r r' : « obr »}
        → (fl : « l ∙ ⇔ ∙ l' »)
        → (fr : « r ∙ ⇔ ∙ r' »)
        → « Square 
            (PairRightIso (fl MkPairIso fr)) fr
            (l PairRightCorrectIso r) (l' PairRightCorrectIso r') »

      -- TODO relation Pair/Iso