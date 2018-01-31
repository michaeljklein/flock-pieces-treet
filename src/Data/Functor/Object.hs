{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}

module Data.Functor.Object where

import Control.Applicative (liftA2)
import Control.Comonad (Comonad(..))
import Data.List.NonEmpty (NonEmpty(..))
import Data.Tuple (swap)
import GHC.Generics (Generic, Generic1)

import Data.Fix (Fix(..), fixList)


-- | Both a right result and a continuation (`Action`).
--
-- Note: I was unable to derive an instance of `Generic1`:
-- @
--  Can't make a derived instance of ‘Generic1 (Object f b)’:
--  Constructor ‘Object’ applies a type to an argument involving the last parameter
--    but the applied type is not of kind * -> *
-- @
--
data Object f b c = Object { getObject :: (  c,  Action f b c)  } deriving (Generic)


-- | An action which could contain a left result, continuation (`Object`)
data Action f b c = Action { runAction ::  f b  (Object f b c)  } deriving (Generic)

deriving instance Functor (f b) => Generic1 (Action f b)



instance Functor (f b) => Functor (Object f b) where
  fmap f (Object (x, xs)) = Object (f x, fmap f xs)

instance Functor (f b) => Functor (Action f b) where
  fmap f (Action xs) = Action (fmap f <$> xs)



instance Comonad (f b) => Comonad (Object f b) where
  extract = fst . getObject

  duplicate x@(Object (_, ys)) = Object (x, const x <$> ys)


instance Comonad (f b) => Comonad (Action f b) where
  extract = extract . extract . runAction

  duplicate x@(Action xs) = Action $ fmap (const x) <$> xs


-- | Cycle a pair, resulting in a fixed point
cyclePair :: Object (,) a b -> Fix ((,) (a, b))
cyclePair (Object (x, Action (y, zs))) = Fix ((y, x), cyclePair zs)

-- | @`fixList` . `cyclePair`@
cyclePairList :: Object (,) a b -> [(a, b)]
cyclePairList = fixList . cyclePair


-- | Given all the functional pairs to define a function, we can cyclically wrap the pairs into an `Action` over pairs.
--
-- Consider generalizing to other nice @(* -> * -> *)@'s
fromAll :: NonEmpty (a, b) -> Action (,) a b
fromAll (x :| xs) = loop x xs
  where
    loop (y, z) (w:ws) = Action (y, Object (z, loop w ws))
    loop (   _) (  _ ) = loop x xs

-- | interesting..
ish :: (a -> b -> (a', b')) -> NonEmpty a -> NonEmpty b -> Action (,) a' b'
ish f xs ys = fromAll (liftA2 f xs ys)

-- | Effectively define `fst` for an `Action` over pairs, using all cases
fstIsh :: NonEmpty a -> NonEmpty b -> Action (,) (a, b) a
fstIsh = ish (\x y -> ((x, y), x))

-- | Effectively define `snd` for an `Action` over pairs, using all cases
sndIsh :: NonEmpty a -> NonEmpty b -> Action (,) (a, b) b
sndIsh = ish (\x y -> ((x, y), y))

-- | Since there's only a finite number of a's, we can cycle through til we match, then continue on
appIsh :: (Eq a, Functor (f t)) => Action (,) a b -> Object f t a -> Object f t b
appIsh (Action (x, Object (y, ys))) (Object (x', Action zs))
  | x == x'    = Object (y, Action (appIsh ys <$> zs))
  | otherwise = appIsh ys (Object (x', Action zs))



-- | Undo an `Action`
unAction :: Functor (f b) => Action f b c -> f b c
unAction = fmap (fst . getObject) . runAction

-- | Undo an `Object`
unObject :: Functor (f b) => Object f b c -> (f b c, c)
unObject = swap . fmap unAction . getObject

-- | Convert to an `Action`
toAction :: Functor (f b) => f b c -> Action f b c
toAction x = Action (toObject x <$> x)

-- | Convert to an `Object`
toObject :: Functor (f b) => f b c -> c -> Object f b c
toObject y x = Object (x, toAction y)


-- | `toAction`
fstAction :: Functor (f (b, c)) => f (b, c) b -> Action f (b, c) b
fstAction = toAction

-- | `toObject`
fstObject :: Functor (f (b, c)) => f (b, c) b -> b -> Object f (b, c) b
fstObject = toObject


-- | `toAction`
sndAction :: Functor (f (b, c)) => f (b, c) c -> Action f (b, c) c
sndAction = toAction

-- | `toObject`
sndObject :: Functor (f (b, c)) => f (b, c) c -> c -> Object f (b, c) c
sndObject = toObject


-- | `toAction`
swapAction :: Functor (f (b, c)) => f (b, c) (c, b) -> Action f (b, c) (c, b)
swapAction = toAction

-- | `toObject`
swapObject :: Functor (f (b, c)) => f (b, c) (c, b) -> (c, b) -> Object f (b, c) (c, b)
swapObject = toObject


-- | `toAction`
mapEitherAction :: Functor (f (c -> d, Either b c)) => f (c -> d, Either b c) (Either b d) -> Action f (c -> d, Either b c) (Either b d)
mapEitherAction = toAction

-- | `toObject`
mapEitherObject :: Functor (f (c -> d, Either b c)) => f (c -> d, Either b c) (Either b d) -> Either b d -> Object f (c -> d, Either b c) (Either b d)
mapEitherObject = toObject


