module FreeSmart.FiniteComplete where

open import Structs.LayerDef
open import Structs.CatDefs

mutual

  private syntax Term tag = / tag /

  infixr 2 _:>_
  infixl 4 _##_
  infix  6 _~>_
  infixl 7 _,_
  infixl 8 _0$_ 

  --
  -- internal types of terms
  --
  data Tag 
      {level : Level} 
      (cat : CatRec level) :
      (layer : Layer) ->
      Set level
    where

      -- objects
      Ob : 

        ----------
        Tag cat L2

      -- morphisms between terms
      _~>_ : 

        {layer : Layer} ->
        {tag : Tag cat (LSucc layer)} ->
        (source target : / tag /) -> 
        --------------------------------
        Tag cat layer

      -- commutative squares
      Square : 

        {layer : Layer} ->
        {tag : Tag cat (LSucc layer)} ->
        {a a' b b' : / tag /} -> 
        (f : / a ~> b /) -> 
        (f' : / a' ~> b' /) ->
        (ma : / a ~> a' /) -> 
        (mb : / b ~> b' /) ->
        ----------------------
        Tag cat layer

      -- (meta)exponent
      _:>_ : 

        {layer : Layer} ->
        (u v : Tag cat layer) ->
        --------------------------
        Tag cat layer

      -- (meta)product
      _##_ :

        {layer : Layer} ->
        (u v : Tag cat layer) ->
        --------------------------
        Tag cat layer


  --
  -- terms of internal types
  --
  data Term
      {level : Level} 
      {cat : CatRec level} : 
      {layer : Layer} ->
      Tag cat layer ->
      Set level
    where
      
      --=======================================================
      -- category structure
      --=======================================================

      -- application of functor
      _0$_ : 

        {layer : Layer} ->
        {u v : Tag cat layer} ->
        / u :> v / ->
        / u / ->
        ---------------
        / v /

      -- lift of functor for act on morphisms
      Mor : 

        {layer : Layer} ->
        {u v : Tag cat (LSucc layer)} ->
        (f : / u :> v /) ->
        {x y : / u /} ->
        ------------------------------
        / x ~> y :> f 0$ x ~> f 0$ y /

      -- pair of elements as element of (meta)product
      _,_ : 

        {layer : Layer} ->
        {u v : Tag cat layer} ->
        / u / ->
        / v / ->
        ------------------------
        / u ## v /
      
      -- pair of morphisms
      Pair : 

        {layer : Layer} ->
        {u v : Tag cat (LSucc layer)} ->
        {l l' : / u /} ->
        {r r' : / v /} ->
        ------------------------------------------
        / l ~> l' ## r ~> r' :> l , r ~> l' , r' /

      -- identity morphism 
      Id : 

        {layer : Layer} ->
        {tag : Tag cat (LSucc layer)} ->
        (o : / tag /) ->
        ----------------
        / o ~> o /

      -- composition of morphisms 
      Mul : 

        {layer : Layer} ->
        {tag : Tag cat (LSucc layer)} ->
        {a b c : / tag /} ->
        -------------------------
        / a ~> b ##
          b ~> c :>
          a ~> c /

      -- inverse equivalence (symmetry) 
      InvEqu : 

        {layer : Layer} ->
        {tag : Tag cat (LSucc (LSucc layer))} ->
        {a b : / tag /} ->
        {f g : / a ~> b /} ->
        / f ~> g / -> 
        ------------------
        / g ~> f /

      -- identity morphism is left neutral 
      IdMorLeftNeutrEqu : 

        {layer : Layer} ->
        {tag : Tag cat (LSucc (LSucc layer))} ->
        {a b : / tag /} ->
        (f : / a ~> b /) ->
        ------------------------------
        /((Id a) Mul f) ~> f /

      -- identity morphism is right neutral 
      IdMorRightNeutrEqu : 

        {layer : Layer} ->
        {tag : Tag cat (LSucc (LSucc layer))} ->
        {a b : / tag /} ->
        (f : / a ~> b /) ->
        ------------------------------
        /(f Mul (Id b)) ~> f /

      -- composition of morphisms is associative 
      MulMorAssocEqu : 

        {layer : Layer} ->
        {tag : Tag cat (LSucc (LSucc layer))} ->
        {a b c d : / tag /} -> 
        (f : / a ~> b /) -> 
        (g : / b ~> c /) -> 
        (h : / c ~> d /) -> 
        -----------------------------
        /((f Mul g) Mul h) ~> 
          (f Mul (g Mul h))/

      --=======================================================
      -- commutative squares structure
      --=======================================================

      -- commutative square
      EquSquare : 

        {layer : Layer} ->
        {tag : Tag cat (LSucc (LSucc layer))} ->
        {a a' b b' : / tag /} -> 
        {f : / a ~> b /} -> 
        {f' : / a' ~> b' /} ->
        {ma : / a ~> a' /} -> 
        {mb : / b ~> b' /} ->
        / (f Mul mb) ~> (ma Mul f') / ->
        ---------------------------------------
        / Square f f' ma mb /

      -- identity square (helper)
      IdSquare : 

        {layer : Layer} ->
        {tag : Tag cat (LSucc (LSucc layer))} ->
        {a b : / tag /} -> 
        (f : / a ~> b /) -> 
        ----------------------------------
        / Square f f (Id a) (Id b) /

      -- identity square (helper)
      IdSquare' : 

        {layer : Layer} ->
        {tag : Tag cat (LSucc (LSucc layer))} ->
        {a b : / tag /} -> 
        (f : / a ~> b /) -> 
        ----------------------------------
        / Square (Id a) (Id b) f f /

      -- composition square (helper)
      _MulSquare_ : 

        {layer : Layer} ->
        {tag : Tag cat (LSucc (LSucc layer))} ->
        {a a' a'' b b' b'' : / tag /} ->
        {f : / a ~> b /} -> 
        {f' : / a' ~> b' /} -> 
        {f'' : / a'' ~> b'' /} ->
        {ma : / a ~> a' /} -> 
        {mb : / b ~> b' /} ->
        {ma' : / a' ~> a'' /} -> 
        {mb' : / b' ~> b'' /} ->
        (sq : / Square f f' ma mb /) ->
        (sq' : / Square f' f'' ma' mb' /) ->
        ------------------------------------------------
        / Square f f'' (ma Mul ma') (mb Mul mb') /

      -- extract equality from square 
      SquareEqu : 

        {layer : Layer} ->
        {tag : Tag cat (LSucc (LSucc layer))} ->
        {a a' b b' : / tag /} -> 
        {f : / a ~> b /} -> 
        {f' : / a' ~> b' /} -> 
        {ma : / a ~> a' /} -> 
        {mb : / b ~> b' /} -> 
        / Square f f' ma mb / -> 
        ----------------------------------
        /(f Mul mb) ~> (ma Mul f')/

      --=======================================================
      -- global monad structure
      --=======================================================

      -- preexistent objects 
      PureOb : 

        CatOb cat -> 
        -------------------------
        / Ob /

      -- preexistent morphisms 
      PureMor : 

        {a b : CatOb cat} ->
        a CatMor b -> 
        ---------------------------
        /(PureOb a) ~> (PureOb b)/

      -- preexistent equivalences 
      PureEqu : 

        {a b : CatOb cat} ->
        {f g : a CatMor b} ->
        f CatEqu g ->
        -----------------------------
        /(PureMor f) ~> (PureMor g)/

      -- restore preexistent identity morphisms 
      PureIdEqu : 

        (a : CatOb cat) ->
        -----------------------
        / PureMor (CatId a) ~> 
          Id (PureOb a) /

      -- restore preexistent multiplication of morphisms 
      _PureMulEqu_ : 

        {a b c : CatOb cat} ->
        (f : a CatMor b) -> 
        (g : b CatMor c) ->
        ------------------------------------
        / PureMor (f CatMul g) ~> 
          ((PureMor f) Mul (PureMor g)) /

      --=======================================================
      -- terminal object structure
      --=======================================================

      -- terminal object
      TerminalOb : 

        ------
        / Ob /

      -- morphism to terminal object 
      TerminalMor : 

        (o : / Ob /) ->
        --------------------
        / o ~> TerminalOb /

      -- terminal morphism is natural 
      TerminalMorNatSquare : 

        {a b : / Ob /} ->
        (f : / a ~> b /) ->
        --------------------
        / Square
          f 
          (Id TerminalOb)
          (TerminalMor a)
          (TerminalMor b) /

      -- terminal morphism is unique 
      --(triangle equality of adjunction) 
      TerminalTriangleEqu : 

        ----------------------------
        / TerminalMor TerminalOb ~> 
          Id TerminalOb /

      --=======================================================
      -- binary product structure
      --=======================================================

      -- cartesian product of objects 
      _ProductOb_ : 

        (l r : / Ob {cat = cat}/) ->
        -----------------
        / Ob /

      -- cartesian product is functor 
      _ProductMor_ : 

        {l l' r r' : / Ob /} ->
        / l ~> l' / -> 
        / r ~> r' / ->
        ---------------------------------------
        /(l ProductOb r) ~> (l' ProductOb r')/

      -- left projection of product 
      _ProjectLeftMor_ : 

        (l r : / Ob /) ->
        ------------------------
        /(l ProductOb r) ~> l /

      -- right projection of product
      _ProjectRightMor_ : 

        (l r : / Ob /) ->
        ------------------------
        /(l ProductOb r) ~> r /

      -- diagonal morphism of product 
      DiagonalMor : 

        (o : / Ob /) ->
        ------------------------
        / o ~> (o ProductOb o)/

      -- left projection of product is natural 
      ProjectLeftMorNatSquare : 

        {l r l' r' : / Ob /} -> 
        (ml : / l ~> l' /) -> 
        (mr : / r ~> r' /) ->
        --------------------------
        / Square
          (ml ProductMor mr)
          ml
          (l ProjectLeftMor r) 
          (l' ProjectLeftMor r') /

      -- right projection of product is natural 
      ProjectRightMorNatSquare : 

        {l r l' r' : / Ob /} -> 
        (ml : / l ~> l' /) -> 
        (mr : / r ~> r' /) ->
        ---------------------------------------------------
        / Square
          (ml ProductMor mr)
          mr
          (l ProjectRightMor r)
          (l' ProjectRightMor r') /

      -- diagonal of product is natural 
      DiagonalMorNatSquare : 

        {a b : / Ob /} ->
        (f : / a ~> b /) ->
        -----------------------------------------
        / Square
          f
          (f ProductMor f)
          (DiagonalMor a)
          (DiagonalMor b) /

      -- cartesian product acts as congruence 
      ProductEqu : 

        {l l' r r' : / Ob /} ->
        {ml ml' : / l ~> l' /} -> 
        (mr mr' : / r ~> r' /) ->
        / ml ~> ml' / -> 
        / mr ~> mr' / ->
        ---------------------------------------------
        /(ml ProductMor mr) ~> (ml' ProductMor mr')/

      -- product is functorial on identities 
      _ProductIdEqu_ : 

        (l r : / Ob /) ->
        --------------------------------
        / (Id l ProductMor Id r) 
            ~> 
          Id (l ProductOb r) /

      -- product is functorial on composition 
      ProductMulEqu : 

        {la lb lc ra rb rc : / Ob /} ->
        (lf : / la ~> lb /) -> 
        (lg : / lb ~> lc /) -> 
        (rf : / ra ~> rb /) -> 
        (rg : / rb ~> rc /) ->
        --------------------------------------------------
        / ((lf Mul lg) ProductMor (rf Mul rg)) 
            ~> 
          ((lf ProductMor rf) Mul (lg ProductMor rg)) /

      -- 1st triangle of product adjunction 
      ProductTriangleEqu : 

        (l r : / Ob /) ->
        --------------------------------------------------------
        / (DiagonalMor (l ProductOb r)
            Mul 
          ((l ProjectLeftMor r) ProductMor (l ProjectRightMor r))) 
              ~> 
          Id (l ProductOb r) /

      -- 2nd triangle of product adjunction 
      ProductTriangleLeftEqu : 

        (o : / Ob /) ->
        ---------------------------------------------
        / (DiagonalMor o Mul (o ProjectLeftMor o)) 
            ~> 
          Id o /

      -- 2nd triangle of product adjunction OK
      ProductTriangleRightEqu : 

        (o : / Ob /) ->
        --------------------------------------------
        / (DiagonalMor o Mul (o ProjectRightMor o)) 
            ~> 
          Id o /

      --=======================================================
      -- binary product structure
      --=======================================================

      -- equalizer object 
      _EqualizerOb_ : 

        {a b : / Ob {cat = cat}/} ->
        (f g : / a ~> b /) ->
        ------------------
        / Ob /

      -- equalizer is functor 
      _EqualizerMor_ : 

        {a a' b b' : / Ob /} ->
        {f g : / a ~> b /} -> 
        {f' g' : / a' ~> b' /} ->
        {ma : / a ~> a' /} -> 
        {mb : / b ~> b' /} ->
        / Square f f' ma mb / ->
        / Square g g' ma mb / ->
        -------------------------------------------
        /(f EqualizerOb g) ~> (f' EqualizerOb g')/

      -- the unit of equalizer adjunction OK
      EqualizerUnitMor : 

        (a : / Ob /) ->
        --------------------------------------
        / a ~> (Id a EqualizerOb Id a)/

      -- the counit of equalizer adjunction, source 
      _EqualizerCounitSourceMor_ : 

        {a b : / Ob /} ->
        (f g : / a ~> b /) ->
        --------------------------
        /(f EqualizerOb g) ~> a /

      -- the counit of equalizer adjunction, target 
      _EqualizerCounitTargetMor_ : 

        {a b : / Ob /} ->
        (f g : / a ~> b /) ->
        --------------------------
        /(f EqualizerOb g) ~> b /

      -- com.square of equalizer count, left
      _EqualizerCounitLeftSquare_ : 

        {a b : / Ob /} ->
        (f g : / a ~> b /) ->
        ----------------------
        / Square 
          (Id (f EqualizerOb g)) 
          f 
          (f EqualizerCounitSourceMor g) 
          (f EqualizerCounitTargetMor g) /

      -- com.square of equalizer count, right 
      _EqualizerCounitRightSquare_ : 

        {a b : / Ob /} ->
        (f g : / a ~> b /) ->
        ----------------------
        / Square 
          (Id (f EqualizerOb g)) 
          g 
          (f EqualizerCounitSourceMor g) 
          (f EqualizerCounitTargetMor g) /

      -- equalizer unit morphism is natural 
      EqualizerUnitNatSquare : 

        {x y : / Ob /} ->
        (f : / x ~> y /) ->
        --------------------
        / Square
          f
          (IdSquare' f EqualizerMor IdSquare' f)
          (EqualizerUnitMor x)
          (EqualizerUnitMor y) /

      -- the counit of equalizer adjunction, source 
      _EqualizerCounitSourceNatSquare_ : 

        {a a' b b' : / Ob /} ->
        {f g : / a ~> b /} -> 
        {f' g' : / a' ~> b' /} ->
        {ma : / a ~> a' /} -> 
        {mb : / b ~> b' /} ->
        (qf : / Square f f' ma mb /) ->
        (qg : / Square g g' ma mb /) ->
        -------------------------------
        / Square
          (qf EqualizerMor qg)
          ma
          (f EqualizerCounitSourceMor g)
          (f' EqualizerCounitSourceMor g') /

      -- the counit of equalizer adjunction, target 
      _EqualizerCounitTargetNatSquare_ : 

        {a a' b b' : / Ob /} ->
        {f g : / a ~> b /} -> 
        {f' g' : / a' ~> b' /} ->
        {ma : / a ~> a' /} -> 
        {mb : / b ~> b' /} ->
        (qf : / Square f f' ma mb /) ->
        (qg : / Square g g' ma mb /) ->
        -------------------------------
        / Square
          (qf EqualizerMor qg)
          mb
          (f EqualizerCounitTargetMor g)
          (f' EqualizerCounitTargetMor g') /

      -- equalizer acts as congruence 
      _EqualizerEqu_ : 

        {a a' b b' : / Ob /} ->
        {f g : / a ~> b /} -> 
        {f' g' : / a' ~> b' /} ->
        {ma ma' : / a ~> a' /} -> 
        {mb mb' : / b ~> b' /} ->
        {ef : / Square f f' ma mb /} ->
        {ef' : / Square f f' ma' mb' /} ->
        {eg : / Square g g' ma mb /} ->
        {eg' : / Square g g' ma' mb' /} ->
        (ea : / ma ~> ma' /) -> 
        (eb : / mb ~> mb' /) -> 
        -------------------------------------------------
        /(ef EqualizerMor eg) ~> (ef' EqualizerMor eg')/

      -- equalizer is functorial on identities 
      _EqualizerIdEqu_ : 

        {a b : / Ob /} ->
        (f g : / a ~> b /) -> 
        --------------------------------------
        / (IdSquare f EqualizerMor IdSquare g) 
            ~> 
          Id (f EqualizerOb g) /

      -- equalizer is functorial on composition 
      EqualizerMulEqu : 

        {a a' a'' b b' b'' : / Ob /} ->
        {f g : / a ~> b /} -> 
        {f' g' : / a' ~> b' /} -> 
        {f'' g'' : / a'' ~> b'' /} ->
        {ma : / a ~> a' /} -> 
        {mb : / b ~> b' /} ->
        {ma' : / a' ~> a'' /} -> 
        {mb' : / b' ~> b'' /} ->
        (ef : / Square f f' ma mb /) ->
        (eg : / Square g g' ma mb /) ->
        (ef' : / Square f' f'' ma' mb' /) ->
        (eg' : / Square g' g'' ma' mb' /) ->
        ----------------------------------------------------
        / ((ef EqualizerMor eg) Mul (ef' EqualizerMor eg'))
            ~> 
          ((ef MulSquare ef') EqualizerMor (eg MulSquare eg')) /

      -- equalizer, 1st triangle 
      EqualizerTriangle1Equ : 

        (x : / Ob /) ->
        --------------------------------------------------------------------
        / (EqualizerUnitMor x Mul (Id x EqualizerCounitSourceMor Id x))
            ~> 
          Id x /

      -- equalizer, 2nd triangle 
      EqualizerTriangle2Equ : 

        {a b : / Ob /} ->
        (f g : / a ~> b /) ->
        ----------------------------------
        / (EqualizerUnitMor (f EqualizerOb g) 
            Mul 
          ((f EqualizerCounitLeftSquare g) EqualizerMor (f EqualizerCounitRightSquare g)))
              ~> 
          Id (f EqualizerOb g) /


--=======================================================

--
-- pack it all into a CatRec
--
FreeFCCat : {level : Level} -> CatRec level -> CatRec level
FreeFCCat cat = record {
    cOb = Term (Ob {cat = cat});
    cMor = \a b -> Term (a ~> b);
    cEqu = \_ _ -> \f g -> Term (f ~> g);
    cId = Id;
    cMul = \_ _ _ -> _Mul_
  }

