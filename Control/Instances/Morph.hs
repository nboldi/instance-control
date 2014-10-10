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

-- test6 :: Monad m => m a -> MaybeT m a
-- test6 = morph

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
  
instance ( fl ~ (ShortestMorph (ToMorphRepo DB) x y)
         , GeneratableMorph DB fl
         , Morph' fl x y
         ) => Morph x y where
  morph = repr (generateMorph db :: fl)
  
class Morph' fl x y where
  repr :: fl -> x a -> y a
  
instance Morph' r y z => Morph' (ConnectMorph x y :+: r) x z where
  repr (ConnectMorph m :+: r) = repr r . m
 
instance (Morph' r m x, Monad m) => Morph' (IdentityMorph (Simple m) :+: r) Identity x where
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
           -- :+: ConnectMorph_mt MaybeT 
           :+: ConnectMorph Maybe [] 
           :+: ConnectMorph_2m [] ListT
           :+: ConnectMorph (MaybeT IO) (ListT IO)
           :+: NoMorph
 
db :: DB 
db = ConnectMorph_2m (MaybeT . return) 
       -- :+: ConnectMorph_mt (MaybeT . liftM Just) 
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

data Simple (a :: * -> *)
data ForAny
data Forall1 (a :: k -> * -> *)

data IdentityMorph m = IdentityMorph
data MUMorph m = MUMorph
  
type family GetMorphSource c :: * where
  GetMorphSource (ConnectMorph m m') = Simple m
  GetMorphSource (ConnectMorph_2m m m') = Simple m
  GetMorphSource (ConnectMorph_mt mt) = ForAny
    
type family GetMorphEnd c :: * where
  GetMorphEnd (ConnectMorph m m') = Simple m'
  GetMorphEnd (ConnectMorph_2m m mt) = Forall1 mt
  GetMorphEnd (ConnectMorph_mt mt) = Forall1 mt
  
type family MonomorphEnd c v :: * where
  MonomorphEnd (ConnectMorph_2m m m') v = ConnectMorph m v
  MonomorphEnd (ConnectMorph_mt t) (t m) = ConnectMorph m (t m)
  MonomorphEnd c v = c
  
type family MatchMorph (m1 :: *) (m2 :: *) :: Bool where
  MatchMorph m m = True
  MatchMorph ForAny m = True
  MatchMorph m ForAny = True
  MatchMorph (Forall1 k) (Simple (k x)) = True
  MatchMorph (Simple (k x)) (Forall1 k) = True
  MatchMorph m1 m2 = False

type family FilterIsMorphFrom (m :: *) (ls :: [*]) :: [*] where
  FilterIsMorphFrom m '[] = '[]
  FilterIsMorphFrom m (c ': ls) = IfThenElse (MatchMorph m (GetMorphSource c)) 
                                             (c ': FilterIsMorphFrom m ls) 
                                             (FilterIsMorphFrom m ls)
  
type family FilterNotElem (h :: [k]) (ls :: [k]) :: [k] where
  FilterNotElem h '[] = '[]
  FilterNotElem h (e ': ls) = IfThenElse (Elem e h) (FilterNotElem h ls) (e ': FilterNotElem h ls) 
          
type family MinByCmpLen (ls :: [k]) :: k where
  MinByCmpLen (e ': ls) = MinByCmpLenDef ls e 
  
type family MinByCmpLenDef (ls :: [k]) (def :: k) :: k where
  MinByCmpLenDef '[] def = def
  MinByCmpLenDef (e ': ls) def = MinByCmpLenDef ls (IfThenElse (Length e <=? Length def) e def)

type family ShortestMorph db a b where
  ShortestMorph db a b = ToMorphStep (Revert (ConcreteMorph b 
                            (Revert (MinByCmpLen (GenMorph '[] db (Simple a) (Simple b))))))

type family ConcreteMorph b ls where
  ConcreteMorph b (c ': r) = ConcreteMorphRest (MonomorphEnd c b ': r)
  ConcreteMorph b ls = ConcreteMorphRest ls
  
type family ConcreteMorphRest (ls :: [*]) :: [*] where
  ConcreteMorphRest '[] = '[]
  ConcreteMorphRest ((ConnectMorph a b) ': c ': r) 
    = (ConnectMorph a b) ': ConcreteMorphRest (MonomorphEnd c a ': r)
  ConcreteMorphRest (e ': ls) = e ': ConcreteMorphRest ls
  
type family ToMorphStep ls where
  ToMorphStep '[] = NoMorph
  ToMorphStep (c ': ls) = c :+: ToMorphStep ls


type family GenMorph h r (a :: *) (b :: *) :: [[*]] where
  GenMorph h r (Simple Identity) m = '[ '[ IdentityMorph m ] ]
  GenMorph h r m (Simple Proxy) = '[ '[ MUMorph m ] ]
  GenMorph h r a b = IfThenElse (MatchMorph a b) '[ '[] ] 
                       (ConcatMapContinueMorph h r a b 
                          (FilterNotElem h (FilterIsMorphFrom a r)))
  
type family ConcatMapContinueMorph h r (a :: *) (b :: *) ls where
  ConcatMapContinueMorph h r a b (c ': ls) = ContinueMorph h r a b c :++: ConcatMapContinueMorph h r a b ls
  ConcatMapContinueMorph h r a b '[] = '[]
  
type family ContinueMorph (h :: [*]) (r :: [*]) (a :: *) (b :: *) (mr :: *) :: [[*]] where
  ContinueMorph h r a b c 
    = MapAppend c (GenMorph (a ': h) r (GetMorphEnd c) b)

         


