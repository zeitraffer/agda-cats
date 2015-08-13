{-# OPTIONS --type-in-type --copatterns #-}

module Setoid1 where

----------------------------------------------------

Type : Set
Type = Set

Relation-Type : (U ob : Type) -> Type
Relation-Type U ob = (src dst : ob) -> U

----------------------------------------------------

record 0,1-Graph-Class (univ : Type) (ob : Type) : Type
  where
  constructor Mk
  field relation : Relation-Type univ ob

record 0,1-Graph-Record (univ : Type) : Type
  where
  constructor Mk
  field {ob} : Type
  field class : 0,1-Graph-Class univ ob

_=>_ :
    {univ ob : Type} ->
    {{graph : 0,1-Graph-Class univ ob}} ->
    Relation-Type univ ob
_=>_ {{graph}} = 0,1-Graph-Class.relation graph

co-map :
    {U1 U2 ob : Type} ->
    (U1 -> U2) ->
    0,1-Graph-Class U1 ob ->
    0,1-Graph-Class U2 ob
co-map f graph = Mk \ a b -> f (a => b)

contra-map :
    {U ob1 ob2 : Type} ->
    (ob1 -> ob2) ->
    0,1-Graph-Class U ob2 ->
    0,1-Graph-Class U ob1
contra-map f graph = Mk \ a b -> (f a => f b)

----------------------------------------------------

instance
  Type/0,1-Graph : 0,1-Graph-Class Type Type
  Type/0,1-Graph = Mk \ src dst -> (src -> dst)

instance
  Type-0,1-Graph : 0,1-Graph-Record Type
  Type-0,1-Graph = Mk Type/0,1-Graph

test : Type
test = Type => Type -- use Type/0-Graph

---------------------------------------------------

record Ind-0,1-Graph-Class
    {ob : Type}
    (univ : 0,1-Graph-Class Type ob)
    : Type
  where
  constructor Mk
  field relation : (src dst : ob) -> (src => dst)

----------------------------------------------------

record 0,0-Graph-Class
    {univ : Type}
    (univ/01-graph : 0,1-Graph-Class Type univ)
    {ob : Type}
    (ob/01-graph : 0,1-Graph-Class univ ob)
    : Type
  where
  constructor Mk
  field inverse : (a b : ob) -> ((a => b) => (b => a))

record 0,0-Graph-Record
    {univ : Type}
    (univ/01-graph : 0,1-Graph-Class Type univ)
    : Type
  where
  constructor Mk
  field {ob} : Type
  field {ob/01-graph} : 0,1-Graph-Class univ ob
  field class : 0,0-Graph-Class univ/01-graph ob/01-graph

---------------------------------------------------

record 1,2-Graph-Class
    {ob : Type}
    {ob/0-graph : 0,1-Graph-Class ob}
    (ob/ind-0-graph : Ind-0,1-Graph-Class (co-map 0,1-Graph-Class ob/0-graph))
    : Type
  where
  constructor Mk

record 1,2-Graph-Record : Type
  where
  constructor Mk
  field {ob} : Type
  field {ob/0-graph} : 0,1-Graph-Class ob
  field {ob/ind-0-graph} : Indexed-0,1-Graph-Class (co-map 0,1-Graph-Class ob/0-graph)
  field class : 1,2-Graph-Class ob/ind-0-graph

---------------------------------------------------
