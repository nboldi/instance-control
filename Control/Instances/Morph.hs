{-# LANGUAGE TypeFamilies, DataKinds, TypeOperators, MultiParamTypeClasses
           , FlexibleInstances, PolyKinds, UndecidableInstances, AllowAmbiguousTypes
           , RankNTypes, ScopedTypeVariables, FlexibleContexts, ConstraintKinds #-}

module Control.Instances.Morph (GenMorph(..), DB, db, Morph, morph) where

import Control.Instances.ShortestPath

import Control.Monad.Identity
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.List
import Data.Maybe
import Data.Proxy

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
type Morph m1 m2 = GenMorph DB m1 m2

-- | Lifts the first monad into the second.
morph :: Morph m1 m2 => m1 a -> m2 a
morph = genMorph db

-- instance GenMorph DB m1 m2 => Morph m1 m2 where
--   morph = genMorph db

-- | A generalized version of 'Morph'. Can work on different
-- rulesets, so this should be used if the ruleset is to be extended.
type GenMorph db m1 m2 = ( CorrectPath m1 m2 (Path db m1 m2)
                         , GeneratableMorph db (Path db m1 m2)
                         , Morph' (Path db m1 m2) m1 m2
                         )

type Path db m1 m2 = TransformPath (PathFromList (ShortestPath (ToMorphRepo db) m1 m2))

-- | Lifts the first monad into the second.
genMorph :: forall db m1 m2 a . GenMorph db m1 m2 => db -> m1 a -> m2 a
genMorph db = repr (generateMorph db :: (Path db m1 m2))

class Morph' fl x y where
  repr :: fl -> x a -> y a

instance Morph' r y z => Morph' (ConnectMorph x y :+: r) x z where
  repr (ConnectMorph m :+: r) = repr r . m

instance (Morph' r m x, Monad m) => Morph' (IdentityMorph m :+: r) Identity x where
  repr (IdentityMorph :+: r) = (repr r :: forall a . m a -> x a) . return . runIdentity

instance Morph' (MUMorph m :+: r) m Proxy where
  repr (MUMorph :+: _) = const Proxy

instance Morph' NoMorph x x where
  repr _ = id

infixr 6 :+:
data a :+: r = a :+: r

data NoMorph = NoMorph

type family ToMorphRepo db where
  ToMorphRepo (cm :+: r) = TranslateConn cm ': ToMorphRepo r
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

-- | This class provides a way to construct the value-level transformations
-- from the type-level path and a rulebase.
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

-- | This class extracts a given morph from the set of rules
class HasMorph r m where
  getMorph :: r -> m
instance {-# OVERLAPPING #-} Monad k => HasMorph (ConnectMorph_2m a b :+: r) (ConnectMorph a (b k)) where
  getMorph (ConnectMorph_2m f :+: _) = ConnectMorph f
instance {-# OVERLAPPING #-} Monad k => HasMorph (ConnectMorph_mt t :+: r) (ConnectMorph k (t k)) where
  getMorph (ConnectMorph_mt f :+: _) = ConnectMorph f
instance {-# OVERLAPS #-} HasMorph r m => HasMorph (c :+: r) m where
  getMorph (_ :+: r) = getMorph r
instance {-# OVERLAPPABLE #-} HasMorph (m :+: r) m where
  getMorph (c :+: _) = c

-- | Checks if the path is found to provide usable error messages
class CorrectPath from to path

instance CorrectPath from to (a :+: b)
instance CorrectPath from to NoMorph

data ConnectMorph m1 m2 = ConnectMorph (forall a . m1 a -> m2 a)
data ConnectMorph_2m m1 m2 = ConnectMorph_2m (forall a k . Monad k => m1 a -> m2 k a)
data ConnectMorph_mt mt = ConnectMorph_mt (forall a k . Monad k => k a -> mt k a)
data IdentityMorph (m :: * -> *) = IdentityMorph
data MUMorph m = MUMorph

-- | Transforms a path element from the generic format to the specific one
type family TranslateConn m where
  TranslateConn (ConnectMorph m1 m2) = Connect m1 m2
  TranslateConn (ConnectMorph_2m m1 m2) = Connect_2m m1 m2
  TranslateConn (ConnectMorph_mt mt) = Connect_mt mt

-- | Transforms the path from the generic format to the specific one
type family TransformPath m where
  TransformPath (Connect m1 m2 :+: r) = ConnectMorph m1 m2 :+: TransformPath r
  TransformPath (Connect_id m :+: r) = IdentityMorph m :+: TransformPath r
  TransformPath (Connect_MU m :+: r) = MUMorph m :+: TransformPath r
  TransformPath NoMorph = NoMorph
  TransformPath NoPathFound = NoPathFound

type family PathFromList ls where
  PathFromList '[] = NoMorph
  PathFromList '[ NoPathFound ] = NoPathFound
  PathFromList (c ': ls) = c :+: PathFromList ls
