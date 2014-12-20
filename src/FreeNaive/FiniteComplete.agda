module FreeNaive.FiniteComplete where

open import Structs.CatDefs

mutual

  --
  -- `Ob cat` - objects of the category
  --
  data Ob 

      {level : Level} 
      (cat : CatRec level) : 
      ------------------------------------
      Set level

    where

      -- preexistent objects
      PureOb : 

        CatOb cat -> 
        ------------
        Ob cat

      -- terminal object
      TerminalOb : 

        ------
        Ob cat

      -- cartesian product of objects
      _ProductOb_ : 

        (l r : Ob cat) ->
        -----------------
        Ob cat

      -- equalizer object
      _EqualizerOb_ : 

        {a b : Ob cat} ->
        (f g : a Mor b) ->
        ------------------
        Ob cat


  --
  -- `Mor` - morphisms between objects
  --
  data _Mor_ 

      {level : Level} 
      {cat : CatRec level} : 
      (a b : Ob cat) -> 
      ------------------------------------
      Set level

    where

      -- preexistent morphisms
      PureMor : 

        {a b : CatOb cat} ->
        a CatMor b -> 
        -------------------------
        (PureOb a) Mor (PureOb b)

      -- identity morphism
      IdMor : 

        (o : Ob cat) ->
        ---------------
        (o Mor o)

      -- composition of morphisms
      _MulMor_ : 

        {a b c : Ob cat} ->
        (a Mor b) -> 
        (b Mor c) ->
        -------------------------
        (a Mor c)
        
      -- morphism to terminal object
      TerminalMor : 

        (o : Ob cat) ->
        ------------------
        (o Mor TerminalOb)

      -- cartesian product is functor
      _ProductMor_ : 

        {l l' r r' : Ob cat} ->
        (l Mor l') -> 
        (r Mor r') ->
        -------------------------------------
        (l ProductOb r) Mor (l' ProductOb r')

      -- left projection of product
      _ProjectLeftMor_ : 

        (l r : Ob cat) ->
        ---------------------
        (l ProductOb r) Mor l

      -- right projection of product
      _ProjectRightMor_ : 

        (l r : Ob cat) ->
        ---------------------
        (l ProductOb r) Mor r

      -- diagonal morphism of product
      DiagonalMor : 

        (o : Ob cat) ->
        ---------------------
        o Mor (o ProductOb o)

      -- equalizer is functor
      _EqualizerMor_ : 

        {a a' b b' : Ob cat} ->
        {f g : a Mor b} -> 
        {f' g' : a' Mor b'} ->
        {ma : a Mor a'} -> 
        {mb : b Mor b'} ->
        MorMor f f' ma mb ->
        MorMor g g' ma mb ->
        -----------------------------------------
        (f EqualizerOb g) Mor (f' EqualizerOb g')

      -- the unit of equalizer adjunction
      EqualizerUnitMor : 

        (a : Ob cat) ->
        --------------------------------
        a Mor (IdMor a EqualizerOb IdMor a)

      -- the counit of equalizer adjunction, source
      _EqualizerCounitSourceMor_ : 

        {a b : Ob cat} ->
        (f g : a Mor b) ->
        -----------------------
        (f EqualizerOb g) Mor a

      -- the counit of equalizer adjunction, target
      _EqualizerCounitTargetMor_ : 

        {a b : Ob cat} ->
        (f g : a Mor b) ->
        -----------------------
        (f EqualizerOb g) Mor b

  --
  -- morphisms in the category of morphisms
  --  
  data MorMor 

      {level : Level} 
      {cat : CatRec level} : 
      {a a' b b' : Ob cat} -> 
      (f : a Mor b) -> 
      (f' : a' Mor b') ->
      (ma : a Mor a') -> 
      (mb : b Mor b') ->
      -------------------------------------
      Set level

    where

      -- commutative square
      SquareMorMor : 

        {a a' b b' : Ob cat} -> 
        {f : a Mor b} -> 
        {f' : a' Mor b'} ->
        {ma : a Mor a'} -> 
        {mb : b Mor b'} ->
        (ma MulMor f') Equ (f MulMor mb) ->
        -----------------------------------
        MorMor f f' ma mb

      -- identity square (helper)
      IdMorMor : 

        {a b : Ob cat} -> 
        (f : a Mor b) -> 
        ------------------------------
        MorMor f f (IdMor a) (IdMor b)

      -- identity square (helper)
      IdMorMor' : 

        {a b : Ob cat} -> 
        (f : a Mor b) -> 
        ------------------------------
        MorMor (IdMor a) (IdMor b) f f

      -- composition square (helper)
      _MulMorMor_ : 

        {a a' a'' b b' b'' : Ob cat} ->
        {f : a Mor b} -> 
        {f' : a' Mor b'} -> 
        {f'' : a'' Mor b''} ->
        {ma : a Mor a'} -> 
        {mb : b Mor b'} ->
        {ma' : a' Mor a''} -> 
        {mb' : b' Mor b''} ->
        (sq : MorMor f f' ma mb) ->
        (sq' : MorMor f' f'' ma' mb') ->
        --------------------------------------------
        MorMor f f'' (ma MulMor ma') (mb MulMor mb')

      -- terminal morphism is natural
      TerminalMorNatMorMor : 

        {a b : Ob cat} ->
        (f : a Mor b) ->
        ------------------
        MorMor
          f 
          (IdMor TerminalOb)
          (TerminalMor a)
          (TerminalMor b) 

      -- left projection of product is natural
      ProjectLeftMorNatMorMor : 

        {l r l' r' : Ob cat} -> 
        (ml : l Mor l') -> 
        (mr : r Mor r') ->
        --------------------------------------------------
        MorMor
          (ml ProductMor mr)
          ml
          (l ProjectLeftMor r) 
          (l' ProjectLeftMor r')

      -- right projection of product is natural
      ProjectRightMorNatMorMor : 

        {l r l' r' : Ob cat} -> 
        (ml : l Mor l') -> 
        (mr : r Mor r') ->
        ---------------------------------------------------
        MorMor
          (ml ProductMor mr)
          mr
          (l ProjectRightMor r)
          (l' ProjectRightMor r')

      -- diagonal of product is natural
      DiagonalMorNatMorMor : 

        {a b : Ob cat} ->
        (f : a Mor b) ->
        -----------------------------------------
        MorMor
          f
          (f ProductMor f)
          (DiagonalMor a)
          (DiagonalMor b)

      -- com.square of equalizer count, left
      _EqualizerCounitLeftMorMor_ : 

        {a b : Ob cat} ->
        (f g : a Mor b) ->
        ------------------
        MorMor 
          (IdMor (f EqualizerOb g)) 
          f 
          (f EqualizerCounitSourceMor g) 
          (f EqualizerCounitTargetMor g)

      -- com.square of equalizer count, right
      _EqualizerCounitRightMorMor_ : 

        {a b : Ob cat} ->
        (f g : a Mor b) ->
        ------------------
        MorMor 
          (IdMor (f EqualizerOb g)) 
          g 
          (f EqualizerCounitSourceMor g) 
          (f EqualizerCounitTargetMor g)

      -- equalizer unit morphism is natural
      EqualizerUnitNatMorMor : 

        {x y : Ob cat} ->
        (f : x Mor y) ->
        -----------------
        MorMor
          f
          (IdMorMor' f EqualizerMor IdMorMor' f)
          (EqualizerUnitMor x)
          (EqualizerUnitMor y)

      -- the counit of equalizer adjunction, source
      _EqualizerCounitSourceNatMorMor_ : 

        {a a' b b' : Ob cat} ->
        {f g : a Mor b} -> 
        {f' g' : a' Mor b'} ->
        {ma : a Mor a'} -> 
        {mb : b Mor b'} ->
        (qf : MorMor f f' ma mb) ->
        (qg : MorMor g g' ma mb) ->
        -----------------------
        MorMor
          (qf EqualizerMor qg)
          ma
          (f EqualizerCounitSourceMor g)
          (f' EqualizerCounitSourceMor g')

      -- the counit of equalizer adjunction, target
      _EqualizerCounitTargetNatMorMor_ : 

        {a a' b b' : Ob cat} ->
        {f g : a Mor b} -> 
        {f' g' : a' Mor b'} ->
        {ma : a Mor a'} -> 
        {mb : b Mor b'} ->
        (qf : MorMor f f' ma mb) ->
        (qg : MorMor g g' ma mb) ->
        -----------------------
        MorMor
          (qf EqualizerMor qg)
          mb
          (f EqualizerCounitTargetMor g)
          (f' EqualizerCounitTargetMor g')


  --
  -- `Equ` - equivalences between morphisms (2-morphisms)
  --
  data _Equ_ 

      {level : Level} 
      {cat : CatRec level} : 
      {a b : Ob cat} -> 
      (f g : a Mor b) -> 
      ----------------------
      Set level

    where

      -- preexistent equivalences
      PureEqu : 

        {a b : CatOb cat} ->
        {f g : a CatMor b} ->
        f CatEqu g ->
        ---------------------------
        (PureMor f) Equ (PureMor g)

      -- restore preexistent identity morphisms
      PureIdEqu : 

        (a : CatOb cat) ->
        --------------------------------------
        PureMor (CatId a) Equ IdMor (PureOb a)

      -- restore preexistent multiplication of morphisms
      _PureMulEqu_ : 

        {a b c : CatOb cat} ->
        (f : a CatMor b) -> 
        (g : b CatMor c) ->
        ---------------------------------------------------------
        PureMor (f CatMul g) Equ ((PureMor f) MulMor (PureMor g))

      -- identity equivalence (reflectivity)
      IdEqu : 

        {a b : Ob cat} -> 
        (f : a Mor b) ->
        ----------------
        f Equ f

      -- composition of equivalences (transitivity)
      _MulEqu_ : 

        {a b : Ob cat} ->
        {f g h : a Mor b} ->
        (f Equ g) -> 
        (g Equ h) ->
        --------------------
        f Equ h

      -- inverse equivalence (symmetry)
      InvEqu : 

        {a b : Ob cat} ->
        {f g : a Mor b} ->
        (f Equ g) -> 
        ------------------
        g Equ f

      -- multiplication of morphisms is congruence
      MulMorEqu : 

        {a b c : Ob cat} ->
        {f f' : a Mor b} -> 
        {g g' : b Mor c} ->
        (f Equ f') -> 
        (g Equ g') ->
        -------------------------------
        (f MulMor g) Equ (f' MulMor g')

      -- identity morphism is left neutral
      IdMorLeftNeutrEqu : 

        {a b : Ob cat} ->
        (f : a Mor b) ->
        --------------------------
        ((IdMor a) MulMor f) Equ f

      -- identity morphism is right neutral
      IdMorRightNeutrEqu : 

        {a b : Ob cat} ->
        (f : a Mor b) ->
        --------------------------
        (f MulMor (IdMor b)) Equ f

      -- composition of morphisms is associative
      MulMorAssocEqu : 

        {a b c d : Ob cat} -> 
        (f : a Mor b) -> 
        (g : b Mor c) -> 
        (h : c Mor d) -> 
        ---------------------------------------------------
        ((f MulMor g) MulMor h) Equ (f MulMor (g MulMor h))

      -- terminal morphism is unique (triangle equality of adjunction)
      TerminalTriangleEqu : 

        -------------------------------------------
        TerminalMor TerminalOb Equ IdMor TerminalOb

      -- cartesian product acts as congruence
      ProductEqu : 

        {l l' r r' : Ob cat} ->
        {ml ml' : l Mor l'} -> 
        (mr mr' : r Mor r') ->
        (ml Equ ml') -> 
        (mr Equ mr') ->
        -------------------------------------------
        (ml ProductMor mr) Equ (ml' ProductMor mr')

      -- product is functorial on identities
      _ProductIdEqu_ : 

        (l r : Ob cat) ->
        --------------------------------
        (IdMor l ProductMor IdMor r) 
          Equ 
        IdMor (l ProductOb r)

      -- product is functorial on composition
      ProductMulEqu : 

        {la lb lc ra rb rc : Ob cat} ->
        (lf : la Mor lb) -> 
        (lg : lb Mor lc) -> 
        (rf : ra Mor rb) -> 
        (rg : rb Mor rc) ->
        ----------------------------------------------
        ((lf MulMor lg) ProductMor (rf MulMor rg)) 
          Equ
        ((lf ProductMor rf) MulMor (lg ProductMor rg))

      -- 1st triangle of product adjunction
      ProductTriangleEqu : 

        (l r : Ob cat) ->
        --------------------------------------------------------
        (DiagonalMor (l ProductOb r)
          MulMor 
        ((l ProjectLeftMor r) ProductMor (l ProjectRightMor r))) 
            Equ 
        IdMor (l ProductOb r)

      -- 2nd triangle of product adjunction
      ProductTriangleLeftEqu : 

        (o : Ob cat) ->
        ---------------------------------------------
        (DiagonalMor o MulMor (o ProjectLeftMor o)) 
          Equ 
        IdMor o

      -- 2nd triangle of product adjunction
      ProductTriangleRightEqu : 

        (o : Ob cat) ->
        --------------------------------------------
        (DiagonalMor o MulMor (o ProjectRightMor o)) 
          Equ 
        IdMor o

      -- equalizer acts as congruence
      _EqualizerEqu_ : 

        {a a' b b' : Ob cat} ->
        {f g : a Mor b} -> 
        {f' g' : a' Mor b'} ->
        {ma ma' : a Mor a'} -> 
        {mb mb' : b Mor b'} ->
        {ef : MorMor f f' ma mb} ->
        {ef' : MorMor f f' ma' mb'} ->
        {eg : MorMor g g' ma mb} ->
        {eg' : MorMor g g' ma' mb'} ->
        (ea : ma Equ ma') -> 
        (eb : mb Equ mb') -> 
        -----------------------------------------------
        (ef EqualizerMor eg) Equ (ef' EqualizerMor eg')

      -- equalizer is functorial on identities
      _EqualizerIdEqu_ : 

        {a b : Ob cat} ->
        (f g : a Mor b) -> 
        --------------------------------------
        (IdMorMor f EqualizerMor IdMorMor g) 
          Equ 
        IdMor (f EqualizerOb g)

      -- equalizer is functorial on composition
      EqualizerMulEqu : 

        {a a' a'' b b' b'' : Ob cat} ->
        {f g : a Mor b} -> 
        {f' g' : a' Mor b'} -> 
        {f'' g'' : a'' Mor b''} ->
        {ma : a Mor a'} -> 
        {mb : b Mor b'} ->
        {ma' : a' Mor a''} -> 
        {mb' : b' Mor b''} ->
        (ef : MorMor f f' ma mb) ->
        (eg : MorMor g g' ma mb) ->
        (ef' : MorMor f' f'' ma' mb') ->
        (eg' : MorMor g' g'' ma' mb') ->
        ----------------------------------------------------
        ((ef EqualizerMor eg) MulMor (ef' EqualizerMor eg'))
          Equ
        ((ef MulMorMor ef') EqualizerMor (eg MulMorMor eg'))

--
-- pack it all into a CatRec
--
FreeFCCat : {level : Level} -> CatRec level -> CatRec level
FreeFCCat cat = record {
    cOb = Ob cat;
    cMor = _Mor_;
    cEqu = \_ _ -> _Equ_;
    cId = IdMor;
    cMul = \_ _ _ -> _MulMor_
  }

