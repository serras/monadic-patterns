{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PostfixOperators #-}
module Control.Pattern (
  -- * Fixed point of a functor
  Fix(..)
  -- * Pattern description
, Pattern
, Pattern'(..)
  -- ** Pattern builders
, (@@)
, __
, (?)
, inj
  -- ** Interpretations
, eq
, matches
, match
, Substitution(..)
, unify
  -- * Semirings
, Semiring(..)
, foldPlus
, foldTimes
, SemiringZippy(..)
) where

import Control.Applicative
import Control.Monad
import qualified Data.Map as M
import Data.Void
import GHC.Generics

newtype Pattern  f c k = Pattern { unPattern :: [Pattern' f c k] }
deriving instance (Show c, Show k, Show (f (Pattern f c k))) => Show (Pattern f c k)
data    Pattern' f c k = Hole k
                       | In (f (Pattern f c k))
                       | Capture c (Pattern f c k)
                       | CatchAll
deriving instance (Show c, Show k, Show (f (Pattern f c k))) => Show (Pattern' f c k)

(@@) :: c -> Pattern f c k -> Pattern f c k
c @@ p = Pattern [Capture c p]

__ :: Pattern f c k
__ = Pattern [CatchAll]

(?) :: k -> Pattern f c k
(?) v = Pattern [Hole v]

inj :: f (Pattern f c k) -> Pattern f c k
inj x = Pattern [In x]

instance Functor f => Functor (Pattern f c) where
  fmap = liftM
instance Functor f => Applicative (Pattern f c) where
  (<*>) = ap
  pure  = return
instance Functor f => Alternative (Pattern f c) where
  empty = mzero
  (<|>) = mplus
instance Functor f => Monad (Pattern f c) where
  return  = Pattern . return . Hole
  (Pattern p) >>= f = Pattern $ p >>= \v -> case v of
    Hole k      -> unPattern (f k)
    In t        -> return (In (fmap (>>= f) t))
    Capture c r -> return (Capture c (r >>= f))
    CatchAll    -> return CatchAll
instance Functor f => MonadPlus (Pattern f c) where
  mzero = Pattern []
  (Pattern x) `mplus` (Pattern y) = Pattern (x ++ y)

class Semiring s where
  (.+.), (.*.) :: s -> s -> s
  zero, one    :: s

foldPlus :: Semiring s => [s] -> s
foldPlus = foldr (.+.) zero

foldTimes :: Semiring s => [s] -> s
foldTimes = foldr (.*.) one

class SemiringZippy f where
  together :: Semiring s => (a -> b -> s) -> f a -> f b -> s

  default together :: (Semiring s, Generic1 f, SemiringZippy (Rep1 f))
                   => (a -> b -> s) -> f a -> f b -> s
  together z x y = together z (from1 x) (from1 y)

instance SemiringZippy U1 where
  together _ _ _ = one
instance SemiringZippy V1 where
  together _ _ _ = one
instance Eq c => SemiringZippy (K1 i c) where
  together _ (K1 x) (K1 y) | x == y    = one
                           | otherwise = zero
instance SemiringZippy Par1 where
  together z (Par1 x) (Par1 y) = z x y
instance SemiringZippy f => SemiringZippy (M1 i c f) where
  together z (M1 x) (M1 y) = together z x y
instance (SemiringZippy f, SemiringZippy g) => SemiringZippy (f :+: g) where
  together z (L1 x) (L1 y) = together z x y
  together z (R1 x) (R1 y) = together z x y
  together _ _      _      = zero
instance (SemiringZippy f, SemiringZippy g) => SemiringZippy (f :*: g) where
  together z (x1 :*: x2) (y1 :*: y2) = together z x1 y1 .*. together z x2 y2

-- Equality
newtype Fix f = Fix { unFix :: f (Fix f) }
deriving instance (Show (f (Fix f))) => Show (Fix f)

instance Semiring Bool where
  (.+.) = (||)
  (.*.) = (&&)
  zero  = False
  one   = True

eq :: SemiringZippy f => Fix f -> Fix f -> Bool
eq (Fix x) (Fix y) = together eq x y

-- First you can define directly
-- match :: Pattern f c k -> Fix f -> Bool

-- But if you generalize over semiring, you get
matches :: SemiringZippy f => Pattern f c Void -> Fix f -> Bool
matches = pat (\_ _ -> True)

pat :: (Semiring s, SemiringZippy f)
    => (c -> Fix f -> s) -> Pattern f c Void -> Fix f -> s
pat c (Pattern ps) t = foldPlus $ map (\p -> pat' c p t) ps
pat' :: (Semiring s, SemiringZippy f)
     => (c -> Fix f -> s) -> Pattern' f c Void -> Fix f -> s
pat' _ (Hole _)      _ = error "Matching only works on closed patterns"
pat' c (In p)  (Fix t) = together (pat c) p t
pat' c (Capture v p) t = c v t .*. pat c p t
pat' _ CatchAll      _ = one

instance (Ord k, Monoid v) => Semiring (Maybe (M.Map k v)) where
  zero = Nothing
  one  = Just M.empty
  (Just m) .+. _ = Just m
  Nothing  .+. n = n
  (Just m) .*. (Just n) = Just $ M.unionWith mappend m n
  _        .*. _        = Nothing

match :: (Ord c, SemiringZippy f)
      => Pattern f c Void -> Fix f -> Maybe (M.Map c [Fix f])
match = pat (\v t -> Just (M.singleton v [t]))


data Substitution k v = Fail | Substitution (M.Map k v)
                      deriving Show

instance (Ord k, SemiringZippy f) => Semiring (Substitution k (Pattern f Void k)) where
  zero = Fail
  one  = Substitution M.empty
  (Substitution s) .+. _ = Substitution s
  Fail             .+. t = t
  (Substitution s) .*. (Substitution t)
    = let i = M.intersectionWith (,) s t
       in if M.null i
             then Substitution $ M.union s t
             else let ((_, (l, r)), rest) = M.deleteFindMin i
                      restS = Substitution $ M.union (s M.\\ i) (M.map fst rest)
                      restT = Substitution $ M.union (t M.\\ i) (M.map snd rest)
                      new = unify l r
                   in (new .*. restS) .*. (new .*. restT)
  _                .*. _                = Fail

ppat :: (Ord k, Semiring s, SemiringZippy f)
     => (k -> Pattern f c k -> s) -> Pattern f c k -> Pattern f c k -> s
ppat c (Pattern ps) (Pattern ts) = foldPlus $ [ppat' c p t | p <- ps, t <- ts]
ppat' :: (Ord k, Semiring s, SemiringZippy f)
      => (k -> Pattern f c k -> s) -> Pattern' f c k -> Pattern' f c k -> s
ppat' _ (Capture _ _) _ = error "Capture is not allowed here"
ppat' _ _ (Capture _ _) = error "Capture is not allowed here"
ppat' _ CatchAll      _ = error "Catch-all is not allowed here"
ppat' _ _      CatchAll = error "Catch-all is not allowed here"
ppat' c (Hole x) (Hole y) | x == y    = one
                          | x < y     = c x (Pattern [Hole y])
                          | otherwise = c y (Pattern [Hole x])
ppat' c (Hole x) t = c x (Pattern [t])
ppat' c t (Hole y) = c y (Pattern [t])
ppat' c (In p) (In t) = together (ppat c) p t

unify :: (Ord k, SemiringZippy f)
      => Pattern f Void k -> Pattern f Void k -> Substitution k (Pattern f Void k)
unify = ppat (\v t -> Substitution $ M.singleton v t)


-- Examples
data Tree' t = Leaf' | Branch' Integer t t
             deriving (Show, Functor, Generic1)
type Tree = Fix Tree'
instance SemiringZippy Tree'

data VarName = X | Y | Z deriving (Show, Eq, Ord)

pattern L = Fix Leaf'
pattern B n l r = Fix (Branch' n l r)

pattern L_ = Pattern [In Leaf']
pattern B_ n l r = Pattern [In (Branch' n l r)]
