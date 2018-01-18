{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Data.Rope where

import Control.Category (Category(..))
import Control.Comonad (Comonad(..))
import Data.Biapplicative (Biapplicative(..), biliftA2)
import Data.Bifunctor (Bifunctor(..))
import Data.Functor.Classes (Eq2(..), Ord2(..), Show2(..), eq2, compare2, showsPrec2)
import Data.Monoid ((<>))
import Prelude hiding (unlines, lines, id, (.))
import Data.Bidistributable (Swap(..))


-- | This is a fun data type, later called.. a "Chain"
newtype Rope p a b = Rope { pullRope :: p a (Rope p b a) }


-- | `undefined`
--
-- @
--  [Either a b] -> Rope Either [a] [b]
-- @
--
goalRope :: f (p a b) -> Rope p (f a) (f b)
goalRope = undefined



instance Eq2 p => Eq2 (Rope p) where
  liftEq2 f g (Rope x) (Rope y) = liftEq2 f (liftEq2 g f) x y

instance (Eq2 p, Eq a, Eq b) => Eq (Rope p a b) where
  (==) = eq2

instance Ord2 p => Ord2 (Rope p) where
  liftCompare2 f g (Rope x) (Rope y) = liftCompare2 f (liftCompare2 g f) x y

instance (Ord2 p, Ord a, Ord b) => Ord (Rope p a b) where
  compare = compare2

instance Show2 p => Show2 (Rope p) where
  liftShowsPrec2 sf f sg g n (Rope x) = liftShowsPrec2 sf f (liftShowsPrec2 sg g sf f) (liftShowList2 sg g sf f) n x

instance (Show2 p, Show a, Show b) => Show (Rope p a b) where
  showsPrec = showsPrec2

instance Bifunctor p => Bifunctor (Rope p) where
  bimap f g (Rope x) = Rope (bimap f (bimap g f) x)

instance Bifunctor p => Functor (Rope p a) where
  fmap = second


instance Biapplicative p => Biapplicative (Rope p) where
  bipure x y = Rope (bipure x (bipure y x))

  (<<*>>) :: Rope p (a -> b) (c -> d) -> Rope p a c -> Rope p b d
  Rope f <<*>> Rope x = Rope (biliftA2 ($) (<<*>>) f x)


instance (Biapplicative p, Monoid a) => Applicative (Rope p a) where
  pure = bipure mempty

  (<*>) :: Rope p a (b -> c) -> Rope p a b -> Rope p a c
  Rope f <*> Rope x = Rope (biliftA2 (<>) (biliftA2 ($) (<>)) f x)


-- | For:
--
-- @
--  instance Swap Iso'
-- @
--
-- But this doesn't seem to work either:
--
-- @
-- instance Swap NIso where
--   swap = NIso . from . getNIso
-- @
--
-- newtype NIso a b = NIso { getNIso :: Iso' a b }


-- | `Twist` a binary type operator into a `Rope`
class Twist f p where
  twist :: f (p a b) -> Rope p (f a) (f b)

instance Functor f => Twist f (,) where
  twist xs = Rope (fst <$> xs, twist (swap <$> xs))

instance Comonad f => Twist f Either where
  twist :: f (Either a b) -> Rope Either (f a) (f b)
  twist xs = Rope $ case extract xs of
                      Left  _ -> Left  . fmap (\(~(Left y)) -> y) $ xs
                      Right _ -> Right . Rope . Left . fmap (\(~(Right y)) -> y) $ xs




