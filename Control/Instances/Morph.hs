{-# LANGUAGE TypeFamilies, DataKinds, TypeOperators, MultiParamTypeClasses, FlexibleInstances, PolyKinds, UndecidableInstances, AllowAmbiguousTypes, RankNTypes, ScopedTypeVariables, FlexibleContexts #-}

module Control.Instances.Morph where

import Control.Monad.Identity
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.List
import Data.Maybe
import GHC.TypeLits
import Control.Instances.TypeLevelPrelude

class Morph x y where
  repr :: x a -> y a
  
instance (fl ~ (ShortestMorph DB x y), Morph' fl x y) => Morph x y where
  repr = repr' (undefined :: fl) -- generateMorph
  
class Morph' fl x y where
  repr' :: fl -> x a -> y a
  
instance Morph' r y z => Morph' (MorphStep x y r) x z where
  repr' (MorphStep m r) = repr' r . m
  
instance Morph' CloseMorph x x where
  repr' fl = id
  

data DBRepoAdd a b r = DBRepoAdd (forall x . a x -> b x) r
data EmptyDBRepo = EmptyDBRepo
  
type family ToMorphRepo db where
  ToMorphRepo (DBRepoAdd a b r) = ConnectMorph a b ': ToMorphRepo r
  ToMorphRepo EmptyDBRepo = '[]

  
type DB = '[ ConnectMorph Identity Maybe
           , ConnectMorph Identity IO
           , ConnectMorph Maybe (MaybeT IO)
           , ConnectMorph Maybe [] 
           , ConnectMorph [] (ListT IO)
           , ConnectMorph (MaybeT IO) (ListT IO)
           ]

-- | A simple connection between two types
data ConnectMorph m1 m2 = ConnectMorph (forall a . m1 a -> m2 a)
  
-- | Records that a given type is already visited by instance search
data VisitedType (m :: * -> *)

class GeneratedMorph db m where
  generateMorph :: db -> m

data MorphStep a b r = MorphStep (forall x . a x -> b x) r
data CloseMorph
  

type family FilterIsMorphFrom (m :: * -> *) (ls :: [k]) :: [k] where
  FilterIsMorphFrom m '[] = '[]
  FilterIsMorphFrom m ((ConnectMorph m m') ': ls) = (ConnectMorph m m') ': FilterIsMorphFrom m ls
  FilterIsMorphFrom m (e ': ls) = FilterIsMorphFrom m ls
  
type family FilterNotElem (h :: [k]) (ls :: [k]) :: [k] where
  FilterNotElem h '[] = '[]
  FilterNotElem h (e ': ls) = IfThenElse (Elem e h) (FilterNotElem h ls) (e ': FilterNotElem h ls) 
          
type family MinByCmpLen (ls :: [k]) :: k where
  MinByCmpLen (e ': ls) = MinByCmpLenDef ls e 
  
type family MinByCmpLenDef (ls :: [k]) (def :: k) :: k where
  MinByCmpLenDef '[] def = def
  MinByCmpLenDef (e ': ls) def = MinByCmpLenDef ls (IfThenElse (Length e <=? Length def) e def)
   

type family ShortestMorph db a b where
  ShortestMorph db a b = ToMorphStep (MinByCmpLen (GenMorph '[] db a b))
          
type family ToMorphStep ls where
  ToMorphStep '[] = CloseMorph
  ToMorphStep (ConnectMorph a b ': ls) = MorphStep a b (ToMorphStep ls)


type family GenMorph h r a b :: [[*]] where
  GenMorph h r a a = '[ '[] ]
  GenMorph h r a b = ConcatMapContinueMorph h r b (FilterNotElem h (FilterIsMorphFrom a r))
  
type family ContinueMorph (h :: [*]) (r :: [*]) (b :: * -> *) (mr :: *) :: [[*]] where
  ContinueMorph h r b (ConnectMorph a x) 
    = MapAppend (ConnectMorph a x) (GenMorph (VisitedType a ': h) r x b)
  
type family ConcatMapContinueMorph h r b ls where
  ConcatMapContinueMorph h r b (c ': ls) = ContinueMorph h r b c :++: ConcatMapContinueMorph h r b ls
  ConcatMapContinueMorph h r b '[] = '[]
         



