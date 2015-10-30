{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE PatternSynonyms #-}
module Control.Pattern.Automata (
  Transition
, Automata(..)
, QTerm(..)
, right
, accepts
, apply
) where

import Control.Pattern
import Data.Bifunctor
import Data.Either

type Transition q f = forall a. q (f a) -> [f (q a)]
data Automata q f = Automata { initial    :: forall a. a -> [q a]
                             , transition :: Transition q f }

data QTerm q f = InF (f (QTerm q f))
               | InQ (q (Fix f))

right :: Traversable f => QTerm q f -> Either (QTerm q f) (Fix f)
right (InF f) = bimap (const (InF f)) Fix $ traverse right f
right (InQ q) = Left (InQ q)

accepts :: (Functor q, Traversable f) => Automata q f -> Fix f -> Bool
accepts auto term = accepts' initials
  where initials = InQ <$> initial auto term
        accepts' []     = False
        accepts' qterms = let nexts = concatMap (apply (transition auto)) qterms
                              (continues, ends) = partitionEithers (right <$> nexts)
                           in not (null ends) || accepts' continues

apply :: (Functor q, Traversable f)
      => Transition q f -> QTerm q f -> [QTerm q f]
apply t (InF x) = InF <$> traverse (apply t) x
apply t (InQ y) = InF . fmap InQ <$> t (fmap (\(Fix t) -> t) y)


-- EXAMPLE

data List_ l = Cons_ Integer l | Nil_ deriving (Functor, Foldable, Traversable)
type List = Fix List_
pattern C x xs = Fix (Cons_ x xs)
pattern N      = Fix Nil_

data State x = CheckTwo x deriving Functor
checkTwo :: Automata State List_
checkTwo = Automata { initial = \x -> [CheckTwo x]
                    , transition = \x -> case x of
                        (CheckTwo Nil_) -> [Nil_]
                        (CheckTwo (Cons_ 2 xs)) -> [Cons_ 2 (CheckTwo xs)]
                        _ -> [] }
