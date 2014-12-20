module FreeSmart.FiniteComplete where

open import Structs.CatDefs

      ----------------------------------
      -- here is our list of structure markers 
      -- (all constructors below are classified by these markers)
      ----
      -- : global monad structure :
      -- : terminal object structure :
      -- : cartesian product structure :
      -- : category of pairs structure :

mutual

  -------------------------------------------------------------------------
  --                                                                     --
  -- the free FC category comprises of `Ob`, `Mor`, `Equ`                --
  --                                                                     --
  -------------------------------------------------------------------------

  --
  -- `Ob cat` - objects of the free FC category
  --
  data Ob {level : Level} (cat : CatRec level) 
      : Set level
    where

      ------------------------------
      -- : global monad structure :
      --

      -- global monad unit, object layer
      PureOb : 

        CatOb cat -> 
        ------------
        Ob cat        

      -- product functor, object layer
      ProductOb : 

        {len : MyNat} ->
        SeqOb cat len ->
        ----------------
        Ob cat

{-
      ---------------------------------
      -- : terminal object structure :
      --

      -- the terminal object
      TerminalOb : 

        ------
        Ob cat

      -----------------------------------
      -- : cartesian product structure :
      --

      -- the cartesian product of objects
      _ProductOb_ : 

        (l r : Ob cat) ->
        -----------------
        Ob cat

      ---------------------------
      -- : equalizer structure :
      --

      -- the equalizer object
      _EqualizerOb_ : 

        {a b : Ob cat} ->
        (f g : a Mor b) ->
        ------------------
        Ob cat
-}  
  -- end data Ob

  --
  -- `Mor` - morphisms between objects
  --
  data _Mor_ {level : Level} {cat : CatRec level} : 
      (a b : Ob cat) -> Set level
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

      -- product functor, morphism layer
      ProductMor : 

        {len : MyNat} ->
        {as bs : SeqOb cat len} ->
        as SeqMor bs ->
        ---------------------------------
        (ProductOb as) Mor (ProductOb bs)

  {-
      -- morphism to terminal object
      TerminalMor : 
          (o : Ob cat) ->
        (o Mor TerminalOb)

      -- cartesian product is functor
      _ProductMor_ : 
          {l l' r r' : Ob cat} ->
          (l Mor l') -> (r Mor r') ->
        (l ProductOb r) Mor (l' ProductOb r')

      -- left projection of product
      _ProjectLeftMor_ : 
          (l r : Ob cat) ->
        (l ProductOb r) Mor l

      -- right projection of product
      _ProjectRightMor_ : 
          (l r : Ob cat) ->
        (l ProductOb r) Mor r

      -- diagonal morphism of product
      DiagonalMor : 
          (o : Ob cat) ->
        o Mor (o ProductOb o)

      -- equalizer is functor
      _EqualizerMor_ : 
          {a a' b b' : Ob cat} ->
          {f g : a Mor b} -> {f' g' : a' Mor b'} ->
          {ma : a Mor a'} -> {mb : b Mor b'} ->
          MorMor f f' ma mb ->
          MorMor g g' ma mb ->
        (f EqualizerOb g) Mor (f' EqualizerOb g')
-}      
  -- end data Mor

  --
  -- morphisms in the category of morphisms
  --  
  data MorMor {level : Level} {cat : CatRec level} : 
        {a a' b b' : Ob cat} -> 
        (f : a Mor b) -> (f' : a' Mor b') ->
        (ma : a Mor a') -> (mb : b Mor b') ->
      Set level
    where

      -- commutative square
      SquareMorMor : 
          {a a' b b' : Ob cat} -> 
          {f : a Mor b} -> {f' : a' Mor b'} ->
          {ma : a Mor a'} -> {mb : b Mor b'} ->
          (ma MulMor f') Equ (f MulMor mb) ->
        MorMor f f' ma mb

      -- identity square (helper)
      IdMorMor : 
          {a b : Ob cat} -> 
          (f : a Mor b) -> 
        MorMor f f (IdMor a) (IdMor b)

      -- composition square (helper)
      _MulMorMor_ : 
          {a a' a'' b b' b'' : Ob cat} ->
          {f : a Mor b} -> {f' : a' Mor b'} -> {f'' : a'' Mor b''} ->
          {ma : a Mor a'} -> {mb : b Mor b'} ->
          {ma' : a' Mor a''} -> {mb' : b' Mor b''} ->
          (sq : MorMor f f' ma mb) ->
          (sq' : MorMor f' f'' ma' mb') ->
        MorMor f f'' (ma MulMor ma') (mb MulMor mb')

  -- end data MorMor

  --
  -- `Equ` - equivalences between morphisms (2-morphisms)
  --
  data _Equ_ {level : Level} {cat : CatRec level} : 
      {a b : Ob cat} -> (f g : a Mor b) -> Set level
    where

      -- preexistent equivalences
      PureEqu : 
          {a b : CatOb cat} ->
          {f g : a CatMor b} ->
          f CatEqu g ->
        (PureMor f) Equ (PureMor g)

      -- restore preexistent identity morphisms
      PureIdEqu : 
          (a : CatOb cat) ->
        PureMor (CatId a) Equ IdMor (PureOb a)

      -- restore preexistent multiplication of morphisms
      _PureMulEqu_ :
          {a b c : CatOb cat} ->
          (f : a CatMor b) -> (g : b CatMor c) ->
        PureMor (f CatMul g) Equ ((PureMor f) MulMor (PureMor g))

      -- identity equivalence (reflectivity)
      IdEqu : 
          {a b : Ob cat} -> 
          (f : a Mor b) ->
        f Equ f

      -- composition of equivalences (transitivity)
      _MulEqu_ : 
          {a b : Ob cat} ->
          {f g h : a Mor b} ->
          (f Equ g) -> (g Equ h) ->
        f Equ h

      -- inverse equivalence (symmetry)
      InvEqu : 
          {a b : Ob cat} ->
          {f g : a Mor b} ->
          (f Equ g) -> 
        g Equ f

      -- multiplication of morphisms is congruence
      MulMorEqu : 
          {a b c : Ob cat} ->
          {f f' : a Mor b} -> {g g' : b Mor c} ->
          (f Equ f') -> (g Equ g') ->
        (f MulMor g) Equ (f' MulMor g')

      -- identity morphism is left neutral
      IdMorLeftNeutrEqu : 
          {a b : Ob cat} ->
          (f : a Mor b) ->
        ((IdMor a) MulMor f) Equ f

      -- identity morphism is right neutral
      IdMorRightNeutrEqu : 
          {a b : Ob cat} ->
          (f : a Mor b) ->
        (f MulMor (IdMor b)) Equ f

      -- composition of morphisms is associative
      MulMorAssocEqu : 
          {a b c d : Ob cat} ->
          (f : a Mor b) -> (g : b Mor c) -> (h : c Mor d) ->
        ((f MulMor g) MulMor h) Equ (f MulMor (g MulMor h))

      -- product functor, equality layer


{-
      -- terminal morphism is natural
      TerminalMorNatEqu : 
          {a b : Ob cat} ->
          (f : a Mor b) ->
         (f MulMor (TerminalMor b)) Equ TerminalMor a

      -- terminal morphism is unique (triangle equality of adjunction)
      TerminalTriangleEqu : 
        TerminalMor TerminalOb Equ IdMor TerminalOb

      -- cartesian product acts as congruence
      ProductEqu : 
          {l l' r r' : Ob cat} ->
          {ml ml' : l Mor l'} -> (mr mr' : r Mor r') ->
          (ml Equ ml') -> (mr Equ mr') ->
        (ml ProductMor mr) Equ (ml' ProductMor mr')

      -- product is functorial on identities
      _ProductIdEqu_ : 
          (l r : Ob cat) ->
        ((IdMor l) ProductMor (IdMor r)) 
          Equ 
        (IdMor (l ProductOb r))

      -- product is functorial on composition
      ProductMulEqu : 
          {la lb lc ra rb rc : Ob cat} ->
          (lf : la Mor lb) -> (lg : lb Mor lc) -> 
          (rf : ra Mor rb) -> (rg : rb Mor rc) ->
        ((lf MulMor lg) ProductMor (rf MulMor rg)) 
          Equ
        ((lf ProductMor rf) MulMor (lg ProductMor rg))

      -- left projection of product is natural
      ProjectLeftMorNatEqu : 
          {l r l' r' : Ob cat} -> 
          (ml : l Mor l') -> (mr : r Mor r') ->
        ((l ProjectLeftMor r) MulMor ml) 
          Equ
        ((ml ProductMor mr) MulMor (l' ProjectLeftMor r'))

      -- right projection of product is natural
      ProjectRightMorNatEqu : 
          {l r l' r' : Ob cat} -> 
          (ml : l Mor l') -> (mr : r Mor r') ->
        ((l ProjectRightMor r) MulMor mr) 
          Equ
        ((ml ProductMor mr) MulMor (l' ProjectRightMor r'))

      -- diagonal of product is natural
      DiagonalMorNatEqu : 
          {a b : Ob cat} ->
          (f : a Mor b) ->
        ((DiagonalMor a) MulMor (f ProductMor f)) 
          Equ
        (f MulMor (DiagonalMor b))

      -- 1st triangle of product adjunction
      ProductTriangleEqu : 
          (l r : Ob cat) ->
        ((DiagonalMor (l ProductOb r)) MulMor ((l ProjectLeftMor r) ProductMor (l ProjectRightMor r))) 
          Equ 
        (IdMor (l ProductOb r))

      -- 2nd triangle of product adjunction
      ProductTriangleLeftEqu : 
          (o : Ob cat) ->
        ((DiagonalMor o) MulMor (o ProjectLeftMor o)) 
          Equ 
        (IdMor o)

      -- 2nd triangle of product adjunction
      ProductTriangleRightEqu : 
          (o : Ob cat) ->
        ((DiagonalMor o) MulMor (o ProjectRightMor o)) 
          Equ 
        (IdMor o)

      -- equalizer acts as congruence
      _EqualizerEqu_ : 
          {a a' b b' : Ob cat} ->
          {f g : a Mor b} -> {f' g' : a' Mor b'} ->
          {ma ma' : a Mor a'} -> {mb mb' : b Mor b'} ->
          {ef : MorMor f f' ma mb} ->
          {ef' : MorMor f f' ma' mb'} ->
          {eg : MorMor g g' ma mb} ->
          {eg' : MorMor g g' ma' mb'} ->
          (ea : ma Equ ma') -> 
          (eb : mb Equ mb') -> 
        (ef EqualizerMor eg) 
          Equ 
        (ef' EqualizerMor eg')

      -- equalizer is functorial on identities
      _EqualizerIdEqu_ : 
          {a b : Ob cat} ->
          (f g : a Mor b) -> 
        ((IdMorMor f) EqualizerMor (IdMorMor g)) 
          Equ 
        IdMor (f EqualizerOb g)

      -- equalizer is functorial on composition
      EqualizerMulEqu : 
          {a a' a'' b b' b'' : Ob cat} ->
          {f g : a Mor b} -> {f' g' : a' Mor b'} -> {f'' g'' : a'' Mor b''} ->
          {ma : a Mor a'} -> {mb : b Mor b'} ->
          {ma' : a' Mor a''} -> {mb' : b' Mor b''} ->
          (ef : MorMor f f' ma mb) ->
          (eg : MorMor g g' ma mb) ->
          (ef' : MorMor f' f'' ma' mb') ->
          (eg' : MorMor g' g'' ma' mb') ->
        ((ef EqualizerMor eg) MulMor (ef' EqualizerMor eg'))
          Equ
        ((ef MulMorMor ef') EqualizerMor (eg MulMorMor eg'))
-}
  -- end data Equ

  -------------------------------------------------------------------
  --                                                               --
  -- the tuple categories comprises of `SeqOb`, `SeqMor`, `SeqEqu` --
  --                                                               --
  -------------------------------------------------------------------

  --
  -- the sequence category (C^n), object layer
  --
  data SeqOb {level : Level} (cat : CatRec level) 
      : MyNat -> Set level
    where

      -- the empty list of objects
      MkNilOb : 

        ---------------------
        SeqOb cat MkZero

      -- a non-empty list of objects
      _MkConsOb_ : 

        {len : MyNat} ->
        Ob cat ->
        SeqOb cat len ->
        -------------------------
        SeqOb cat (MkSucc len)

  -- end data SeqOb

  --
  -- the sequence category (C^n), morphism layer
  --
  data _SeqMor_ {level : Level} {cat : CatRec level} 
      : {len : MyNat} -> (a b : SeqOb cat len) -> Set level
    where

      -- the empty list of morphisms
      MkNilMor : 

        ----------------------
        MkNilOb SeqMor MkNilOb

      -- a non-empty list of morphisms
      _MkConsMor_ : 

        {len : MyNat} ->
        {a b : Ob cat} ->
        {as bs : SeqOb cat len} ->
        a Mor b ->
        as SeqMor bs ->
        --------------------------------------
        (a MkConsOb as) SeqMor (b MkConsOb bs)

  -- end data _SeqMor_

  --
  -- the sequence category (C^n), equality layer
  --
  data _SeqEqu_ {level : Level} {cat : CatRec level} 
      : {len : MyNat} -> {a b : SeqOb cat len} -> (f g : a SeqMor b) -> Set level
    where

      -- the empty list of morphisms
      MkNilEqu : 

        ------------------------
        MkNilMor SeqEqu MkNilMor

      -- a non-empty list of morphisms
      _MkConsEqu_ : 

        {len : MyNat} ->
        {a b : Ob cat} ->
        {as bs : SeqOb cat len} ->
        {f g : a Mor b} ->
        {fs gs : as SeqMor bs} ->
        f Equ g ->
        fs SeqEqu gs ->
        ----------------------------------------
        (f MkConsMor fs) SeqEqu (g MkConsMor gs)

  -- end data _SeqMor_

  -- diagonal functor, object layer
  DiagonalOb : 

    {level : Level} ->
    {cat : CatRec level} -> 
    (len : MyNat) ->
    Ob cat ->
    -------------
    SeqOb cat len

  DiagonalOb MkZero _ = MkNilOb
  DiagonalOb (MkSucc len) a = a MkConsOb (DiagonalOb len a)

  -- diagonal functor, morphism layer
  DiagonalMor : 

    {level : Level} ->
    {cat : CatRec level} -> 
    {a b : Ob cat} ->
    (len : MyNat) ->
    a Mor b ->
    --------------------------------------------
    (DiagonalOb len a) SeqMor (DiagonalOb len b)

  DiagonalMor MkZero _ = MkNilMor
  DiagonalMor (MkSucc len) f = f MkConsMor (DiagonalMor len f)

  -- diagonal functor, equality layer
  DiagonalEqu : 

    {level : Level} ->
    {cat : CatRec level} -> 
    {a b : Ob cat} ->
    {f g : a Mor b} ->
    (len : MyNat) ->
    f Equ g ->
    --------------------------------------------
    (DiagonalMor len f) SeqEqu (DiagonalMor len g)

  DiagonalEqu MkZero _ = MkNilEqu
  DiagonalEqu (MkSucc len) e = e MkConsEqu (DiagonalEqu len e)

-------------------------------------------------------------------------------
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

