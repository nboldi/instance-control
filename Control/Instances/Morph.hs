{-# LANGUAGE TypeFamilies, DataKinds, TypeOperators, MultiParamTypeClasses, FlexibleInstances, PolyKinds, UndecidableInstances, AllowAmbiguousTypes, RankNTypes, ScopedTypeVariables, FlexibleContexts, OverlappingInstances #-}

module Control.Instances.Morph (Morph(..)) where

import Control.Monad.Identity
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.List
import Control.Monad.State
import Data.Maybe
import Data.Proxy
import GHC.TypeLits
import Control.Instances.TypeLevelPrelude

test1 :: Identity a -> IO a
test1 = morph

test2 :: Maybe a -> [a]
test2 = morph

test3 :: Maybe a -> ListT IO a
test3 = morph

test4 :: Maybe a -> MaybeT IO a
test4 = morph

test5 :: Monad m => Maybe a -> ListT (StateT s m) a
test5 = morph

-- | States that 'm1' can be represented with 'm2'.
-- That is because 'm2' contains more infromation than 'm1'.
--
-- The 'MMorph' relation defines a natural transformation from 'm1' to 'm2'
-- that keeps the following laws:
--
-- > morph (return x)  =  return x
-- > morph (m >>= f)   =  morph m >>= morph . f
-- 
-- It is a reflexive and transitive relation.
--
class Morph (m1 :: * -> *) (m2 :: * -> *) where
  -- | Lifts the first monad into the second.
  morph :: m1 a -> m2 a
  
instance ( fl ~ (MorphPath (ToMorphRepo DB) x y)
         , GeneratableMorph DB fl
         , Morph' fl x y
         ) => Morph x y where
  morph = repr (generateMorph db :: fl)
  
class Morph' fl x y where
  repr :: fl -> x a -> y a
  
instance Morph' r y z => Morph' (ConnectMorph x y :+: r) x z where
  repr (ConnectMorph m :+: r) = repr r . m
 
instance (Morph' r m x, Monad m) => Morph' (IdentityMorph m :+: r) Identity x where
  repr (IdentityMorph :+: r) = (repr r :: forall a . m a -> x a) . return . runIdentity
  
instance Morph' (MUMorph m :+: r) m Proxy where
  repr (MUMorph :+: _) = const Proxy
 
instance Morph' NoMorph x x where
  repr fl = id
  
infixr 6 :+:
data a :+: r = a :+: r 

data NoMorph = NoMorph
  
type family ToMorphRepo db where
  ToMorphRepo (cm :+: r) = cm ': ToMorphRepo r
  ToMorphRepo NoMorph = '[]
   
type DB = ConnectMorph_2m Maybe MaybeT
           :+: ConnectMorph_mt MaybeT 
           :+: ConnectMorph Maybe [] 
           :+: ConnectMorph_2m [] ListT
           :+: ConnectMorph (MaybeT IO) (ListT IO)
           :+: NoMorph
 
db :: DB 
db = ConnectMorph_2m (MaybeT . return) 
       :+: ConnectMorph_mt (MaybeT . liftM Just) 
       :+: ConnectMorph (maybeToList) 
       :+: ConnectMorph_2m (ListT . return) 
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
instance Monad k => HasMorph (ConnectMorph_mt t :+: r) (ConnectMorph k (t k)) where
  getMorph (ConnectMorph_mt f :+: r) = ConnectMorph f
instance HasMorph r m => HasMorph (c :+: r) m where
  getMorph (c :+: r) = getMorph r

-- | A simple connection between two types
data ConnectMorph m1 m2 = ConnectMorph { fromConnectMorph :: forall a . m1 a -> m2 a }
data ConnectMorph_2m m1 m2 = ConnectMorph_2m { fromConnectMorph_2m :: forall a k . Monad k => m1 a -> m2 k a }
data ConnectMorph_mt mt = ConnectMorph_mt { fromConnectMorph_mt :: forall a k . Monad k => k a -> mt k a }

data IdentityMorph (m :: * -> *) = IdentityMorph
data MUMorph m = MUMorph
  
data NoPathFound


type family MorphPath e s t where
  MorphPath e s t = PathFromList (ShortestPath e s t)
  
type family ShortestPath (e :: [*]) (s :: * -> *) (t :: * -> *) :: [*] where
  ShortestPath e t t = '[]
  ShortestPath e Identity t = '[ IdentityMorph t ]
  ShortestPath e s Proxy = '[ MUMorph s ]
  ShortestPath e s t = ShortestPath' e s (InitCurrent e t)
  
type family ShortestPath' (e :: [*]) (s :: * -> *) (c :: [[*]]) :: [*] where
  ShortestPath' e s '[] = '[ NoPathFound ]
  ShortestPath' e s c = FromMaybe (ShortestPath' e s (ApplyEdges e c c))
                                  (GetFinished s c) 
                                  
                                      
type family GetFinished s c where
  GetFinished s ((ConnectMorph s b ': p) ': lls) 
    = Just (ConnectMorph s b ': p)
  GetFinished s (p ': lls) = GetFinished s lls
  GetFinished s '[] = Nothing

type family InitCurrent (e :: [*]) (t :: * -> *) :: [[*]] where
  InitCurrent '[] t = '[]
  InitCurrent (e ': es) t = IfJust (ApplyEdge e t)
                                   ('[ MonomorphEnd e t ] ': InitCurrent es t) 
                                   (InitCurrent es t)
  
type family ApplyEdges (e :: [*]) (co :: [[*]]) (c :: [[*]]) :: [[*]] where
  ApplyEdges (e ': es) co ((ConnectMorph s b ': p) ': cs) 
    = AppendJust (IfThenJust (IsJust (ApplyEdge e s)) 
                                (MonomorphEnd e s ': ConnectMorph s b ': p)) 
                 (ApplyEdges (e ': es) co cs)
  ApplyEdges (e ': es) co '[] = ApplyEdges es co co
  ApplyEdges '[] co cr = '[]  
  
type family ApplyEdge e t :: Maybe (* -> *) where
  ApplyEdge (ConnectMorph ms mr) mr = Just ms
  ApplyEdge (ConnectMorph_2m ms mt) (mt m) = Just ms
  ApplyEdge (ConnectMorph_mt mt) (mt m) = Just m
  ApplyEdge e t = Nothing

type family MonomorphEnd c v :: * where
  MonomorphEnd (ConnectMorph_2m m m') v = ConnectMorph m v
  MonomorphEnd (ConnectMorph_mt t) (t m) = ConnectMorph m (t m)
  MonomorphEnd c v = c
  
type family PathFromList ls where
  PathFromList '[] = NoMorph
  PathFromList '[ NoPathFound ] = NoPathFound
  PathFromList (c ': ls) = c :+: PathFromList ls


         


