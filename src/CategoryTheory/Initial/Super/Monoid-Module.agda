{-# OPTIONS --type-in-type --copatterns #-}

module CategoryTheory.Initial.Super.Monoid-Module where

mutual

  data Tag : Set 
    where
      PropT : Tag
      0CatT : Tag
      1MonoidT : Tag
      ObPropT : « PropT » -> Tag
      Ob0CatT : « 0CatT » -> Tag

  data «_» : Tag → Set 
    where

      _==_ 
        : {0cat : « 0CatT »} 
        -> (dom cod : « Ob0CatT 0cat ») 
        -> « PropT »
      
      Id0
        : « MonoidId »

