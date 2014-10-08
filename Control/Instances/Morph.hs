{-# LANGUAGE TypeFamilies, DataKinds, TypeOperators, MultiParamTypeClasses, FlexibleInstances, PolyKinds, UndecidableInstances, AllowAmbiguousTypes, RankNTypes, ScopedTypeVariables, FlexibleContexts, OverlappingInstances #-}

module Control.Instances.Morph where

import Control.Monad.Identity
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.List
import Data.Maybe
import GHC.TypeLits
import Control.Instances.TypeLevelPrelude

test1 :: IO String
test1 = repr (Identity "alma")

test2 :: [String]
test2 = repr (Just "alma")

test3 :: ListT IO String
test3 = repr (Just "alma")

test4 :: MaybeT IO String
test4 = repr (Just "alma")


class Morph x y where
  repr :: x a -> y a
  
instance ( fl ~ (ShortestMorph (ToMorphRepo DB) x y)
         , GeneratableMorph DB fl
         , Morph' fl x y
         ) => Morph x y where
  repr = repr' (generateMorph db :: fl)
  
class Morph' fl x y where
  repr' :: fl -> x a -> y a
  
instance Morph' r y z => Morph' (ConnectMorph x y :+: r) x z where
  repr' (ConnectMorph m :+: r) = repr' r . m
 
instance (Morph' r m x, Monad m) => Morph' (IdentityMorph (Simple m) :+: r) Identity x where
  repr' (IdentityMorph :+: r) = (repr' r :: forall a . m a -> x a) . return . runIdentity
  
instance Morph' (MUMorph m :+: r) m MU where
  repr' (MUMorph :+: _) = const MU
 
instance Morph' NoMorph x x where
  repr' fl = id
  
data DBRepoAdd a b r = DBRepoAdd (forall x . a x -> b x) r

infixr 6 :+:
data a :+: r = a :+: r 

data NoMorph = NoMorph
  
type family ToMorphRepo db where
  ToMorphRepo (cm :+: r) = cm ': ToMorphRepo r
  ToMorphRepo NoMorph = '[]
   
type DB = ConnectMorph_2m Maybe MaybeT
           :+: ConnectMorph Maybe [] 
           :+: ConnectMorph [] (ListT IO)
           :+: ConnectMorph (MaybeT IO) (ListT IO)
           :+: NoMorph
 
db :: DB 
db = ConnectMorph_2m (MaybeT . return) 
       :+: ConnectMorph (maybeToList) 
       :+: ConnectMorph (ListT . return) 
       :+: ConnectMorph (ListT . liftM maybeToList . runMaybeT) 
       :+: NoMorph
  
class GeneratableMorph db ch where
  generateMorph :: db -> ch
instance GeneratableMorph db NoMorph where
  generateMorph _ = NoMorph
instance GeneratableMorph db r 
      => GeneratableMorph db ((IdentityMorph m) :+: r) where
  generateMorph db = IdentityMorph :+: generateMorph db
instance GeneratableMorph db r 
      => GeneratableMorph db (MUMorph m :+: r) where
  generateMorph db = MUMorph :+: generateMorph db
instance (HasMorph db (ConnectMorph a b), GeneratableMorph db r) 
      => GeneratableMorph db (ConnectMorph a b :+: r) where
  generateMorph db = getMorph db :+: generateMorph db
  
class HasMorph r m where 
  getMorph :: r -> m
instance HasMorph (m :+: r) m where
  getMorph (c :+: r) = c
instance Monad k => HasMorph (ConnectMorph_2m a b :+: r) (ConnectMorph a (b k)) where
  getMorph (ConnectMorph_2m f :+: r) = ConnectMorph f
instance HasMorph r m => HasMorph (c :+: r) m where
  getMorph (c :+: r) = getMorph r

-- | A simple connection between two types
data ConnectMorph m1 m2 = ConnectMorph { fromConnectMorph :: forall a . m1 a -> m2 a }
data ConnectMorph_2m m1 m2 = ConnectMorph_2m { fromConnectMorph_2m :: forall a k . Monad k => m1 a -> m2 k a }

data Simple (a :: * -> *)
data Forall1M (a :: (* -> *) -> * -> *)

data MU a = MU

data IdentityMorph m = IdentityMorph
data MUMorph m = MUMorph
  
-- | Records that a given type is already visited by instance search
data VisitedType (m :: * -> *)
  

type family FilterIsMorphFrom (m :: *) (ls :: [k]) :: [k] where
  FilterIsMorphFrom m '[] = '[]
  FilterIsMorphFrom (Simple m) ((ConnectMorph m m') ': ls) = (ConnectMorph m m') ': FilterIsMorphFrom (Simple m) ls
  FilterIsMorphFrom (Forall1M k) ((ConnectMorph (k x) m') ': ls) = (ConnectMorph (k x) m') ': FilterIsMorphFrom (Forall1M k) ls
  FilterIsMorphFrom (Simple m) ((ConnectMorph_2m m m') ': ls) = (ConnectMorph_2m m m') ': FilterIsMorphFrom (Simple m) ls
  FilterIsMorphFrom (Forall1M k) ((ConnectMorph_2m (k x) m') ': ls) = (ConnectMorph_2m (k x) m') ': FilterIsMorphFrom (Forall1M k) ls
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
  ShortestMorph db a b = ToMorphStep (Revert (ConcreteMorph (ConcreteMorphStart b 
                            (Revert (MinByCmpLen (GenMorph '[] db (Simple a) (Simple b)))))))

type family ConcreteMorphStart b ls where
  ConcreteMorphStart b ((ConnectMorph_2m x y) ': r) 
    = ((ConnectMorph x b) ': r) 
  ConcreteMorphStart b ls = ls
  
type family ConcreteMorph ls where
  ConcreteMorph '[] = '[]
  ConcreteMorph ((ConnectMorph a b) ': (ConnectMorph_2m c d) ': r) 
    = (ConnectMorph a b) ': ConcreteMorph ((ConnectMorph c a) ': r)
  ConcreteMorph (e ': ls) = e ': ConcreteMorph ls
  
type family ToMorphStep ls where
  ToMorphStep '[] = NoMorph
  ToMorphStep (c ': ls) = c :+: ToMorphStep ls


type family GenMorph h r (a :: *) (b :: *) :: [[*]] where
  GenMorph h r a a = '[ '[] ]
  GenMorph h r (Simple (k x)) (Forall1M k) = '[ '[] ]
  GenMorph h r (Forall1M k) (Simple (k x)) = '[ '[] ]
  GenMorph h r (Simple Identity) m = '[ '[ IdentityMorph m ] ]
  GenMorph h r m (Simple MU) = '[ '[ MUMorph m ] ]
  GenMorph h r a b = ConcatMapContinueMorph h r b (FilterNotElem h (FilterIsMorphFrom a r))
  
type family ContinueMorph (h :: [*]) (r :: [*]) (b :: *) (mr :: *) :: [[*]] where
  ContinueMorph h r b (ConnectMorph a x) 
    = MapAppend (ConnectMorph a x) (GenMorph (VisitedType a ': h) r (Simple x) b)
  ContinueMorph h r b (ConnectMorph_2m a x) 
    = MapAppend (ConnectMorph_2m a x) (GenMorph (VisitedType a ': h) r (Forall1M x) b)
  
type family ConcatMapContinueMorph h r b ls where
  ConcatMapContinueMorph h r b (c ': ls) = ContinueMorph h r b c :++: ConcatMapContinueMorph h r b ls
  ConcatMapContinueMorph h r b '[] = '[]
         


