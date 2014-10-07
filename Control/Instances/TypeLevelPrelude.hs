{-# LANGUAGE TypeFamilies, DataKinds, TypeOperators, MultiParamTypeClasses, FlexibleInstances, PolyKinds, UndecidableInstances, AllowAmbiguousTypes, RankNTypes, ScopedTypeVariables, FlexibleContexts #-}

module Control.Instances.TypeLevelPrelude where

import GHC.TypeLits

type family l1 :++: l2 where
  '[] :++: l2       = l2
  (e ': r1) :++: l2 = e ': (r1 :++: l2)
  
type family Elem e ls where
  Elem e '[] = False
  Elem e (e ': ls) = True
  Elem e (x ': ls) = Elem e ls
  
type family IfThenElse (b :: Bool) (th :: x) (el :: x) :: x where
  IfThenElse True  th el = th
  IfThenElse False th el = el
         
type family Length ls :: Nat where
  Length '[] = 0
  Length (e ': ls) = 1 + Length ls
           
type family MapAppend e lls where
  MapAppend e (ls ': lls) = (e ': ls) ': MapAppend e lls
  MapAppend e '[] = '[]