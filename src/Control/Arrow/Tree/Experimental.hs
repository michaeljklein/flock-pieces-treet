{-# LANGUAGE DataKinds #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Control.Arrow.Tree.Experimental where

import Control.Arrow (Arrow(..))
import Control.Arrow.Tree (ATree(..), AForest(..))
import Control.Category (Category(..))
import Control.Monad.Trans.TreeT (Tree(..), Forest(..))
import Data.Biapplicative hiding (first, second)
import Data.Groupoid (Groupoid(..))
import Data.Profunctor (Profunctor(..), Closed(..), Choice(..))
import GHC.TypeLits (TypeError, ErrorMessage(Text))
import Prelude hiding (fail, id, (.))



-- | @`inv` = `forestInv`@
instance (Arrow t, Groupoid t) => Groupoid (AForest t) where
  inv :: AForest t a b -> AForest t b a
  inv = forestInv

-- | `undefined`
forestInv :: (Arrow t, Groupoid t) => AForest t a b -> AForest t b a
forestInv = undefined

-- | `undefined`
forestInv1 :: (Arrow t, Groupoid t) => Forest (t a) b -> Forest (t b) a
forestInv1 = undefined

-- | `undefined`
forestInv2 :: (Arrow t, Groupoid t) => t a (Tree (t a) b) -> t b (Tree (t b) a)
forestInv2 x = inv (swaps x)

-- | `undefined`
swaps :: Arrow t => t a (Tree (t a) b) -> t (Tree (t b) a) b
swaps = undefined

-- | `undefined`
swaps1 :: Arrow t => t a (b, Forest (t a) b) -> t (a, Forest (t b) a) b
swaps1 = undefined

-- | `undefined`.
-- Ok, I'm convinced that this needs Groupoid
swaps2 :: Arrow t => t a (b, t a (Tree (t a) b)) -> t (a, t b (Tree (t b) a)) b
swaps2 _ = undefined



instance Biapplicative t => Biapplicative (ATree t) where
  bipure x y = ATree (Tree (y, getAForest (bipure x y)))

  ATree (Tree (f, fs)) <<*>> ATree (Tree (x, xs)) = ATree (Tree (f x, getAForest (AForest fs <<*>> AForest xs)))



-- | This also looks a lot like distribution.. (`undefined`)
instance Biapplicative t => Biapplicative (AForest t) where
  bipure x y = AForest (Forest (bipure x (getATree (bipure x y))))

  AForest (Forest fs) <<*>> AForest (Forest xs) = AForest (Forest (undefined fs <<*>> xs))
        -- _ :: t (a -> b) (Tree (t (a -> b)) (c -> d)) -> t (a -> b) (Tree (t a) c -> Tree (t b) d)


-- | This is harder than I thought, might be impossible, probably impossible.
--
-- Try extending @Choice (ATree t)@ to not use @Choice (AForest t)@.
--
-- (Currently, both are `undefined`.)
instance Choice t => Choice (AForest t) where
  left' :: AForest t a b -> AForest t (Either a c) (Either b c)
  left' (AForest (Forest xs)) = AForest (Forest (rmap (either (getATree . left' . ATree) (\x -> Tree (Right x, Forest undefined))) (left' xs)))
  -- left' :: Forest (t a) b -> Forest (t (Either a c)) (Either b c)
  -- left' :: t a (Tree (t a) b) -> t (Either a c) (Tree (t (Either a c)) (Either b c))

  right' :: AForest t a b -> AForest t (Either c a) (Either c b)
  right' = undefined
  -- right' :: Forest (t a) b -> Forest (t (Either c a)) (Either c b)
  -- right' :: t a (Tree (t a) b) -> t (Either c a) (Tree (t (Either c a)) (Either b c))


instance Closed t => Closed (ATree t) where
  closed :: ATree t a b -> ATree t (x -> a) (x -> b)
  closed (ATree (Tree (x, xs))) = ATree (Tree (const x, getAForest (closed (AForest xs))))
  -- closed :: Tree (t a) b -> Tree (t (x -> a)) (x -> b)
  -- closed :: (b, Forest (t a) b) -> (x -> b, Forest (t (x -> a)) (x -> b))

-- | REQUIRES DISTRIBUTION: distribute :: Functor f => f (g a) -> g (f a), Functor f => f (Tree m a) -> Tree m (f a)
instance Closed t => Closed (AForest t) where
  closed :: AForest t a b -> AForest t (x -> a) (x -> b)
  closed (AForest (Forest xs)) = AForest (Forest (undefined $ closed xs))
  -- closed :: Forest (t a) b -> Forest (t (x -> a)) (x -> b)
  -- closed :: t a (Tree (t a) b) -> t (x -> a) (Tree (t (x -> a)) (x -> b))




-- | `undefined`
wantTo :: AForest t a (ATree t a b) -> AForest t (ATree t a b) b
wantTo = undefined

-- | `undefined`
wantFrom :: AForest t (ATree t a b) b -> AForest t a (ATree t a b)
wantFrom = undefined


-- | Impossible instance, no way to convert @a@ to @b@.
instance (Arrow t, Groupoid t, TypeError ('Text "Impossible instance, no way to convert @a@ to @b@.")) => Groupoid (ATree t) where
  inv :: ATree t a b -> ATree t b a
  inv = error "impossible"



instance Choice t => Choice (ATree t) where
  left' :: ATree t a b -> ATree t (Either a c) (Either b c)
  left' (ATree (Tree (x, xs))) = ATree (Tree (Left x, getAForest (left' (AForest xs))))
  -- left' :: Tree (t a) b -> Tree (t (Either a c)) (Either b c)
  -- left' :: (b, Forest (t a) b) -> (Either b c, Forest (t (Either a c)) (Either b c))

  right' :: ATree t a b -> ATree t (Either c a) (Either c b)
  right' (ATree (Tree (x, xs))) = ATree (Tree (Right x, getAForest (right' (AForest xs))))
  -- right' :: Tree (t a) b -> Tree (t (Either c a)) (Either c b)
  -- right' :: (b, Forest (t a) b) -> (Either c b, Forest (t a) b)



