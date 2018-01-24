{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}

module Control.Monad.Trans.Rope where

import Data.Biapplicative (Biapplicative(..), biliftA2)
import Data.Bifunctor (Bifunctor(..))
import Data.Monoid ((<>))
import Control.Applicative (liftA2)


-- | `Rope` transformer type
newtype RopeT p m a b = RopeT { pullRopeT :: p a (m (RopeT p m b a)) }

instance (Bifunctor p, Functor m) => Bifunctor (RopeT p m) where
  bimap f g = RopeT . bimap f (fmap (bimap g f)). pullRopeT

instance (Bifunctor p, Functor m) => Functor (RopeT p m a) where
  fmap = second


instance (Biapplicative p, Applicative m) => Biapplicative (RopeT p m) where
  bipure x y = RopeT (bipure x (pure (bipure y x)))

  (<<*>>) :: RopeT p m (a -> b) (c -> d) -> RopeT p m a c -> RopeT p m b d
  RopeT f <<*>> RopeT x = RopeT (biliftA2 ($) (liftA2 (<<*>>)) f x)


instance (Biapplicative p, Applicative m, Monoid a) => Applicative (RopeT p m a) where
  pure = bipure mempty

  (<*>) :: RopeT p m a (b -> c) -> RopeT p m a b -> RopeT p m a c
  RopeT f <*> RopeT x = RopeT (biliftA2 (<>) (liftA2 (biliftA2 ($) (<>))) f x)


