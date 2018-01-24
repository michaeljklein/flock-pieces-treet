{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}


module Data.Flip where

import Control.Comonad (Comonad(..))
import Control.Monad (liftM2)
import Data.Coerce (coerce)
import Data.Functor.Contravariant (Contravariant(..))
import Test.QuickCheck (Arbitrary(..), CoArbitrary(..), Testable(..), (.&.))
import Test.QuickCheck.Checkers (EqProp(..), TestBatch, quickBatch)
import Test.QuickCheck.Classes (functor, functorMorphism)


-- | A four-part mutually recursive data type
--
-- Notes:
--
-- Number of cycles:
--   w.l.o.g we require the first element to be the minimum
--
-- @
-- 1 minimum
-- * permutations of all else
-- (n-1)! ?
-- @
--
-- E.g. for two, there's exactly one cycle:
--
-- @
--   Value, Container =>
--     Value * Container (..), Container (Value * ..)
--     Value + Container (..), Container (Value + ..)
-- @
--
-- Interesting example: unary / binary
--
-- @
-- (a -> b)
-- (a -> b -> c)
--
-- a -> b
-- a -> (b -> c)
-- a -> (a, b, b -> c)
-- b -> (b, c)
-- a -> (b, (b -> (c, next)))
-- @
--
--
-- Want:
--
-- Applicative instances for `F1`, `F3`
--
-- `Comonad` instances for `F2`, `F4`
--
newtype F1 a b c = F1 { getF1 :: a -> F2 a b c  }

-- | Continuation of `F1`
newtype F2 a b c = F2 { getF2 :: (b,  F3 a b c) } deriving (Show)

-- | Continuation of `F2`
newtype F3 a b c = F3 { getF3 :: b -> F4 a b c  }

-- | Continuation of `F3`
newtype F4 a b c = F4 { getF4 :: (c,  F1 a b c) } deriving (Show)


-- | I believe the exact list of "free" morphisms between @F@'s is:
--
-- @
-- 1 -> 1          (we don't have an @a@, and F1's the only one that depends directly on @a@)
-- 2 -> 1, 2, 3, 4 (see implementations)
-- 3 -> 3          (as with F1, we don't have @b@..)
-- 4 -> 1, 4       (`snd` gives F1, then we get stuck)
-- @
--
freeMorphismsNotes :: ()
freeMorphismsNotes = ()

-- | `id`
morphF11 :: F1 a b c -> F1 a b c
morphF11 = id

functorMorphF11 :: TestBatch
functorMorphF11 = functorMorphism (morphF11 :: F1 Bool Bool a -> F1 Bool Bool a)

-- | `F2` to `F4`, then `F4` to `F1`
morphF21 :: F2 a b c -> F1 a b c
morphF21 = morphF41 . morphF24

functorMorphF21 :: TestBatch
functorMorphF21 = functorMorphism (morphF21 :: F2 Bool Bool a -> F1 Bool Bool a)

-- | `id`
morphF22 :: F2 a b c -> F2 a b c
morphF22 = id

functorMorphF22 :: TestBatch
functorMorphF22 = functorMorphism (morphF22 :: F2 Bool Bool a -> F2 Bool Bool a)

-- | Get and `snd`
morphF23 :: F2 a b c -> F3 a b c
morphF23 = snd . getF2

functorMorphF23 :: TestBatch
functorMorphF23 = functorMorphism (morphF23 :: F2 Bool Bool a -> F3 Bool Bool a)

-- | Get and apply the @b@ in `F2` to the function in `F3`
morphF24 :: F2 a b c -> F4 a b c
morphF24 = uncurry (flip ($)) . fmap getF3 . getF2

functorMorphF24 :: TestBatch
functorMorphF24 = functorMorphism (morphF24 :: F2 Bool Bool a -> F4 Bool Bool a)


-- | `id`
morphF33 :: F3 a b c -> F3 a b c
morphF33 = id

functorMorphF33 :: TestBatch
functorMorphF33 = functorMorphism (morphF33 :: F3 Bool Bool a -> F3 Bool Bool a)

-- | Get and `snd`
morphF41 :: F4 a b c -> F1 a b c
morphF41 = snd . getF4

functorMorphF41 :: TestBatch
functorMorphF41 = functorMorphism (morphF41 :: F4 Bool Bool a -> F1 Bool Bool a)

-- | `id`
morphF44 :: F4 a b c -> F4 a b c
morphF44 = id

functorMorphF44 :: TestBatch
functorMorphF44 = functorMorphism (morphF44 :: F4 Bool Bool a -> F4 Bool Bool a)



instance Functor (F1 a b) where
  fmap f (F1 x) = F1 (fmap f <$> x)

testF1Functor :: TestBatch
testF1Functor = functor (undefined :: F1 Bool Bool (Int, Int, Int))


instance Functor (F2 a b) where
  fmap f (F2 x) = F2 (fmap f <$> x)

testF2Functor :: TestBatch
testF2Functor = functor (undefined :: F2 Bool Bool (Int, Int, Int))


instance Functor (F3 a b) where
  fmap f (F3 x) = F3 (fmap f <$> x)

testF3Functor :: TestBatch
testF3Functor = functor (undefined :: F3 Bool Bool (Int, Int, Int))


instance Functor (F4 a b) where
  fmap f (F4 (x, xs)) = F4 (f x, fmap f xs)

testF4Functor :: TestBatch
testF4Functor = functor (undefined :: F4 Bool Bool (Int, Int, Int))



instance (Arbitrary a, Show a, Arbitrary b, Eq b, Show b, Eq c) => EqProp (F1 a b c) where
  (F1 fx) =-= (F1 fy) = fx =-= fy

instance (Arbitrary a, Show a, Arbitrary b, Eq b, Show b, Eq c) => EqProp (F2 a b c) where
  (F2 ~(x, xs)) =-= (F2 ~(y, ys)) = property (x == y) .&. (xs =-= ys)

instance (Arbitrary a, Show a, Arbitrary b, Eq b, Show b, Eq c) => EqProp (F3 a b c) where
  (F3 fx) =-= (F3 fy) = fx =-= fy

instance (Arbitrary a, Show a, Arbitrary b, Eq b, Show b, Eq c) => EqProp (F4 a b c) where
  (F4 ~(x, xs)) =-= (F4 ~(y, ys)) = property (x == y) .&. (xs =-= ys)


instance (CoArbitrary a, Arbitrary b, CoArbitrary b, Arbitrary c) => Arbitrary (F1 a b c) where
  arbitrary = F1 <$> arbitrary

instance (CoArbitrary a, Arbitrary b, CoArbitrary b, Arbitrary c) => Arbitrary (F2 a b c) where
  arbitrary = F2 <$> liftM2 (,) arbitrary arbitrary

instance (CoArbitrary a, CoArbitrary b, Arbitrary b, Arbitrary c) => Arbitrary (F3 a b c) where
  arbitrary = F3 <$> arbitrary

instance (CoArbitrary a, CoArbitrary b, Arbitrary b, Arbitrary c) => Arbitrary (F4 a b c) where
  arbitrary = F4 <$> liftM2 (,) arbitrary arbitrary

-- | Stub instance
instance Show (F1 a b c) where
  show x = x `seq` "F1"

-- | Stub instance
instance Show (F3 a b c) where
  show x = x `seq` "F3"



-- | Note that of `F1`, `F2`, `F3`, and `F4`, only `F4` is always a `Comonad` (if @a ~ b ~ c@, for example, I believe `F2` would be one as well):
--
-- `F1` would need `F2` to be a `Comonad`, and a default value for @a@
--
-- `F2` would require `F3` to be a `Comonad`
--
-- `F3` would require a default value for @b@, and for `F4` to be a `Comonad` (which I believe it is)
--
--
-- @
-- extend extract = ext
--   ext (F4 ~(x, xs)) = F4 (x, F1 . fmap (F2 . fmap (F3 . fmap ext . getF3) . getF2) . getF1 $ xs)
--
--   since F1, F2, F3, getF1, getF2, getF3, fmap do not affect the values, aside from @fmap ext@, I believe this may be proof of: ext == id
--
-- extend extract      = id
-- extract . extend f  = f
-- extend f . extend g = extend (f . extend g)
-- @
--
instance Comonad (F4 a b) where
  extract :: F4 a b c -> c
  extract = fst . getF4

  extend :: (F4 a b c -> d) -> F4 a b c -> F4 a b d
  extend f x@(F4 ~(_, xs)) = let y = f x in F4 (y, F1 . fmap (F2 . fmap (F3 . fmap (extend f) . getF3) . getF2) . getF1 $ xs)





-- | Like `flip`
newtype Flip f a b = Flip { getFlip :: f b a } deriving (Eq, Ord, Show, EqProp, Arbitrary)

-- | `coerce`
withFlip :: (Flip f1 a1 b1 -> Flip f a b) -> f1 b1 a1 -> f b a
withFlip = coerce


-- | `Flip` for three arguments
newtype Flip2 f a b c = Flip2 { getFlip2 :: f c b a } deriving (Eq, Ord, Show)

-- | Coerce
withFlip2 :: (Flip2 f1 a1 b1 c1 -> Flip2 f a b c) -> f1 c1 b1 a1 -> f c b a
withFlip2 = coerce


-- | A newtype to ensure generated functions (`Arbitrary`) are inverses of each other
newtype SomeIso a b = SomeIso { getSomeIso :: (b -> a, a -> b) }

-- | Ignore arguments
instance Show (SomeIso a b) where
  show x = x `seq` "SomeIso"

-- | Unsigned integer addition is an inverse to subtraction
instance Arbitrary (SomeIso Word Word) where
  arbitrary = SomeIso . (\x -> ((+ x), (subtract x))) <$> arbitrary


-- | Test `IsoFunctor`
testIsoFunctor :: (IsoFunctor f, EqProp (f a), Show (f a), Arbitrary (SomeIso a a), Arbitrary (f a)) => f a -> TestBatch
testIsoFunctor x_ = ("IsoFunctor", [ ("isomap"
                                     , property (\(SomeIso (f, g)) x -> isomap g f (x `asTypeOf` x_) =-= isomap f g (isomap g f x)))
                                   ])



-- | A "functor" that requires an isomorphism to map over
class IsoFunctor f where
  isomap :: (b -> a) -> (a -> b) -> f a -> f b


instance IsoFunctor (Flip (F1 a) c) where
  isomap f g (Flip (F1 x)) = Flip (F1 (withFlip (isomap f g) <$> x))

-- | Uses `Word`, `testIsoFunctor`
testIsoFunctorF1 :: TestBatch
testIsoFunctorF1 = testIsoFunctor (undefined :: Flip (F1 Word) Word Word)


instance IsoFunctor (Flip (F2 a) c) where
  isomap f g (Flip (F2 (x, xs))) = Flip (F2 (g x, withFlip (isomap f g) xs))

-- | Uses `Word`, `testIsoFunctor`
testIsoFunctorF2 :: TestBatch
testIsoFunctorF2 = testIsoFunctor (undefined :: Flip (F2 Word) Word Word)


instance IsoFunctor (Flip (F3 a) c) where
  isomap f g (Flip (F3 x)) = Flip (F3 (withFlip (isomap f g) . x . f))

-- | Uses `Word`, `testIsoFunctor`
testIsoFunctorF3 :: TestBatch
testIsoFunctorF3 = testIsoFunctor (undefined :: Flip (F3 Word) Word Word)


instance IsoFunctor (Flip (F4 a) c) where
  isomap f g (Flip (F4 x)) = Flip (F4 (withFlip (isomap f g) <$> x))

-- | Uses `Word`, `testIsoFunctor`
testIsoFunctorF4 :: TestBatch
testIsoFunctorF4 = testIsoFunctor (undefined :: Flip (F4 Word) Word Word)



instance Contravariant (Flip2 F1 a b) where
  contramap f (Flip2 (F1 x)) = Flip2 (F1 (withFlip2 (contramap f) . x . f))

instance Contravariant (Flip2 F2 a b) where
  contramap f (Flip2 (F2 x)) = Flip2 (F2 (withFlip2 (contramap f) <$> x))

instance Contravariant (Flip2 F3 a b) where
  contramap f (Flip2 (F3 x)) = Flip2 (F3 (withFlip2 (contramap f) <$> x))

instance Contravariant (Flip2 F4 a b) where
  contramap f (Flip2 (F4 x)) = Flip2 (F4 (withFlip2 (contramap f) <$> x))


-- | All `TestBatch`s
testBatches :: [TestBatch]
testBatches = [ functorMorphF11
              , functorMorphF21
              , functorMorphF22
              , functorMorphF23
              , functorMorphF24
              , functorMorphF33
              , functorMorphF41
              , functorMorphF44
              , testF1Functor
              , testF2Functor
              , testF3Functor
              , testF4Functor
              , testIsoFunctorF1
              , testIsoFunctorF2
              , testIsoFunctorF3
              , testIsoFunctorF4
              ]

-- | Run all test batches using `quickBatch`
quickTestBatches :: IO ()
quickTestBatches = mapM_ quickBatch testBatches



