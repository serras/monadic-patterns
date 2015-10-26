{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
module Control.Pattern.Free where

import Control.Monad
import Control.Monad.Fix
import Control.Monad.Trans.Free
import Data.Void
import GHC.Generics

type Pattern (f :: * -> *) = FreeT f []
type ClosedPattern f = Pattern f Void

newtype Fix f = Fix { unFix :: f (Fix f) }

type Matchable f = (Generic1 f, MatchesG (Rep1 f))

matches :: Matchable f => Pattern f k -> Fix f -> Bool
matches (FreeT ps) t = any (flip matches_ t) ps

matches_ :: Matchable f => FreeF f k (Pattern f k) -> Fix f -> Bool
matches_ (Pure _) _       = error "Matching only works on closed patterns"
matches_ (Free p) (Fix t) = matchesG (from1 p) (from1 t)

class MatchesG f where
  matchesG :: Matchable g => f (Pattern g k) -> f (Fix g) -> Bool

instance MatchesG U1 where
  matchesG _ _ = True
instance MatchesG V1 where
  matchesG _ _ = True
instance MatchesG Par1 where
  matchesG (Par1 p) (Par1 t) = matches p t
instance Eq c => MatchesG (K1 i c) where
  matchesG (K1 p) (K1 t) = p == t
instance MatchesG f => MatchesG (M1 i c f) where
  matchesG (M1 p) (M1 t) = matchesG p t
instance (MatchesG f, MatchesG g) => MatchesG (f :+: g) where
  matchesG (L1 p) (L1 t) = matchesG p t
  matchesG (R1 p) (R1 t) = matchesG p t
  matchesG _      _      = False
instance (MatchesG f, MatchesG g) => MatchesG (f :*: g) where
  matchesG (p1 :*: p2) (t1 :*: t2) = matchesG p1 t1 && matchesG p2 t2


data Tree' r = Leaf'
             | Branch' Integer r r
             deriving (Eq, Functor, Generic1)
type Tree = Fix Tree'

pattern LeafR :: Pattern Tree' k
pattern LeafR = FreeT [Free Leaf']

pattern BranchR :: Integer -> Pattern Tree' k -> Pattern Tree' k -> Pattern Tree' k
pattern BranchR n l r = FreeT [Free (Branch' n l r)]

treeWith2 :: Tree
treeWith2 = Fix (Branch' 2 (Fix (Branch' 2 (Fix Leaf') (Fix Leaf'))) (Fix Leaf'))
treeWith3 :: Tree
treeWith3 = Fix (Branch' 2 (Fix (Branch' 3 (Fix Leaf') (Fix Leaf'))) (Fix Leaf'))

regexWith2 :: ClosedPattern Tree'
regexWith2 = LeafR `mplus` (BranchR 2 regexWith2 regexWith2)
-- regexWith2' :: ClosedPattern Tree'
-- regexWith2' = mfix (\a -> LeafR `mplus` BranchR 2 (return a) (return a))
