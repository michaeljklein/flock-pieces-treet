-- {-# LANGUAGE AllowAmbiguousTypes #-}
-- {-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
-- {-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
-- {-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- {-# LANGUAGE RankNTypes #-}
-- {-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
-- {-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- {-# LANGUAGE DeriveFunctor #-}
-- {-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Control.Monad.Trans.TreeT where

import Control.Applicative (Alternative(..), liftA2)
import Control.Category (Category(..))
import Control.Comonad (Comonad(..), ComonadApply(..))
import Control.Comonad.Trans.Class (ComonadTrans(..))
import Control.Monad hiding (fail)
import Control.Monad.Free.Class (MonadFree(..))
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Primitive (PrimMonad(..), PrimBase(..))
import Control.Monad.State.Class (MonadState(..))
import Control.Monad.Trans.Class (MonadTrans(..))
import Data.Functor.Classes (Eq1(..), Ord1(..))
import Data.Monoid ((<>))
import Data.Semigroup hiding ((<>))
import GHC.Generics (Generic)
import Prelude hiding (fail, id, (.))


-- | A Generalized tree type
--
-- Question: does any property such that
--
-- @
--   Prop :: * -> Constraint
--     Prop a
--       => Prop (Tree Identity a)?
--     Prop a, Prop a + Prop b => Prop (a, b), Prop a => Prop (m a)
--       => Prop (Tree m a)?
--     Prop a => Prop (m a)
--       => Prop (Tree m a)?
--   Prop :: (* -> *) -> Constraint
--     Prop Identity, Prop a + Prop b => Prop (a :*: b), Prop m
--       => Prop (Tree m)?
--     Prop m
--       => Prop (Forest m)?
--   Prop :: (* -> * -> *) -> Constraint
--     Prop (,), Prop t
--       => Prop (ATree t m)?
--     Prop t
--       => Prop (AForest t m)?
-- @
--
-- E.g.
--
-- @
--  instance Alternative m => Alternative (Forest m)@
-- @
--
-- But no instance for @`Tree` m@
--
-- E.g.
--
-- @
--  instance Functor m => Comonad (Tree m)
-- @
--
-- But no instance for @`Forest` m@
--
newtype Tree   m a = Tree   { getTree   :: (a, Forest m a) } deriving (Generic)

-- | The counterpart to `Tree`
newtype Forest m a = Forest { getForest :: m (Tree m a) }    deriving (Generic)



instance Functor m => Functor (Tree m) where
  fmap :: (a -> b) -> Tree m a -> Tree m b
  fmap f (Tree (x, xs)) = Tree (f x, fmap f xs)

instance Functor m => Functor (Forest m) where
  fmap :: (a -> b) -> Forest m a -> Forest m b
  fmap f (Forest x) = Forest (fmap f <$> x)


instance Applicative m => Applicative (Tree m) where
  pure :: a -> Tree m a
  pure x = Tree (x, pure x)

  (<*>) :: Tree m (a -> b) -> Tree m a -> Tree m b
  Tree (f, fs) <*> Tree (x, xs) = Tree (f x, fs <*> xs)

instance Applicative m => Applicative (Forest m) where
  pure :: a -> Forest m a
  pure x = Forest (pure (pure x))

  (<*>) :: Forest m (a -> b) -> Forest m a -> Forest m b
  Forest fs <*> Forest xs = Forest (liftA2 (<*>) fs xs)


instance Monad m => Monad (Tree m) where
  return :: a -> Tree m a
  return x = Tree (x, pure x)

  (>>=) :: Tree m a -> (a -> Tree m b) -> Tree m b
  Tree (x, _) >>= f = f x


instance Monad m => Monad (Forest m) where
  return :: a -> Forest m a
  return x = Forest (return (return x))

  (>>=) :: Forest m a -> (a -> Forest m b) -> Forest m b
  Forest xs >>= f = Forest (join (getForest . f . extract <$> xs))


instance Functor m => Comonad (Tree m) where
  extract :: Tree m a -> a
  extract (Tree (x, _)) = x

  duplicate :: Tree m a -> Tree m (Tree m a)
  duplicate (Tree (x, Forest xs)) = Tree (Tree (x, Forest xs), Forest (duplicate <$> xs))


instance Applicative m => ComonadApply (Tree m) where
  (<@>) :: Tree m (a -> b) -> Tree m a -> Tree m b
  Tree (f, fs) <@> Tree (x, xs) = Tree (f x, fs <*> xs)


instance MonadTrans Forest where
  lift :: Monad m => m a -> Forest m a
  lift = Forest . fmap return


instance MonadIO m => MonadIO (Forest m) where
  liftIO :: IO a -> Forest m a
  liftIO = lift . liftIO


instance MonadState s m => MonadState s (Forest m) where
  get = lift get
  put = lift . put
  state = lift . state


instance ComonadTrans Tree where
  lower :: Comonad w => Tree w a -> w a
  lower = lower . snd . getTree


instance ComonadTrans Forest where
  lower :: Comonad w => Forest w a -> w a
  lower = fmap extract . getForest


instance Eq1 t => Eq1 (Tree t) where
  liftEq f (Tree (x, xs)) (Tree (y, ys)) = f x y && liftEq f xs ys

instance Eq1 t => Eq1 (Forest t) where
  liftEq f (Forest xs) (Forest ys) = liftEq (liftEq f) xs ys


instance Ord1 t => Ord1 (Tree t) where
  liftCompare f (Tree (x, xs)) (Tree (y, ys)) = f x y <> liftCompare f xs ys

instance Ord1 t => Ord1 (Forest t) where
  liftCompare f (Forest xs) (Forest ys) = liftCompare (liftCompare f) xs ys


-- | `Tree` is not a monad transformer, but @`Tree` . m@ is, for @`Monad` m@
liftTree :: Monad m => m a -> m (Tree m a)
liftTree x = Tree <$> fmap (, lift x) x


-- | Push a monadic context into a `Forest` by binding it and unwrapping the forest.
--
-- It should be equivalent to:
--
-- @
--  Forest . join . fmap getForest
--  Forest .        (>>= getForest)
-- @
--
instance Monad m => MonadFree m (Forest m) where
  wrap :: m (Forest m a) -> Forest m a
  wrap fs = Forest (fs >>= getForest)


instance (Monoid a, Applicative m) => Monoid (Tree m a) where
  mempty = Tree (mempty, pure mempty)
  mappend (Tree (x, xs)) (Tree (y, ys)) = Tree (mappend x y, liftA2 mappend xs ys)

instance (Monoid a, Applicative m) => Monoid (Forest m a) where
  mempty = Forest (pure mempty)
  mappend (Forest xs) (Forest ys) = Forest (liftA2 mappend xs ys)


instance (Monoid a, Applicative m) => Semigroup (Tree m a)
instance (Monoid a, Applicative m) => Semigroup (Forest m a)


-- | Note that `Tree` can only be `Alternative` with constraints on @a@, so it
-- can't be `Alternative` in Haskell
instance Alternative m => Alternative (Forest m) where
  empty = Forest empty
  Forest xs <|> Forest ys = Forest (xs <|> ys)


instance PrimMonad m => PrimMonad (Forest m) where
  type PrimState (Forest m) = PrimState m

  primitive = lift . primitive


instance PrimBase m => PrimBase (Forest m) where
  internal = internal . pullMa


instance Foldable m => Foldable (Tree m) where
  foldr f y (Tree (x, xs)) = foldr f (f x y) xs

instance Foldable m => Foldable (Forest m) where
  foldr f y (Forest xs) = foldr (flip (foldr f)) y xs


instance Traversable m => Traversable (Tree m) where
  traverse f (Tree (x, xs)) = Tree <$> liftA2 (,) (f x) (traverse f xs)

  mapM f (Tree (x, xs)) = Tree <$> liftM2 (,) (f x) (mapM f xs)

instance Traversable m => Traversable (Forest m) where
  traverse f (Forest xs) = Forest <$> traverse (traverse f) xs

  mapM f (Forest xs) = Forest <$> mapM (mapM f) xs



instance (Applicative m, Num a) => Num (Tree m a) where
  Tree (x, xs) + Tree (y, ys) = Tree (x + y, xs + ys)
  Tree (x, xs) * Tree (y, ys) = Tree (x * y, xs * ys)
  Tree (x, xs) - Tree (y, ys) = Tree (x - y, xs - ys)

  negate (Tree (x, xs)) = Tree (negate x, negate xs)
  abs    (Tree (x, xs)) = Tree (abs    x, abs    xs)
  signum (Tree (x, xs)) = Tree (signum x, signum xs)

  fromInteger x = Tree (fromInteger x, fromInteger x)


instance (Applicative m, Num a) => Num (Forest m a) where
  Forest xs + Forest ys = Forest (liftA2 (+) xs ys)
  Forest xs * Forest ys = Forest (liftA2 (*) xs ys)
  Forest xs - Forest ys = Forest (liftA2 (-) xs ys)

  negate (Forest xs) = Forest (negate <$> xs)
  abs    (Forest xs) = Forest (abs    <$> xs)
  signum (Forest xs) = Forest (signum <$> xs)

  fromInteger x = Forest (pure (fromInteger x))


instance (Applicative m, Fractional a) => Fractional (Tree m a) where
  Tree (x, xs) / Tree (y, ys) = Tree (x / y, xs / ys)
  recip (Tree (x, xs)) = Tree (recip x, recip xs)
  fromRational x = Tree (fromRational x, fromRational x)

instance (Applicative m, Fractional a) => Fractional (Forest m a) where
  Forest xs / Forest ys = Forest (liftA2 (/) xs ys)
  recip (Forest xs) = Forest (recip <$> xs)
  fromRational x = Forest (pure (fromRational x))


instance (Applicative m, Floating a) => Floating (Tree m a) where
  pi = Tree (pi, pi)

  Tree (x, xs) ** Tree (y, ys) = Tree (x ** y, xs ** ys)
  logBase (Tree (x, xs)) (Tree (y, ys)) = Tree (logBase x y, logBase xs ys)

  exp (Tree (x, xs)) = Tree (exp x, exp xs)
  log (Tree (x, xs)) = Tree (log x, log xs)
  sqrt (Tree (x, xs)) = Tree (sqrt x, sqrt xs)
  sin (Tree (x, xs)) = Tree (sin x, sin xs)
  cos (Tree (x, xs)) = Tree (cos x, cos xs)
  tan (Tree (x, xs)) = Tree (tan x, tan xs)
  asin (Tree (x, xs)) = Tree (asin x, asin xs)
  acos (Tree (x, xs)) = Tree (acos x, acos xs)
  atan (Tree (x, xs)) = Tree (atan x, atan xs)
  sinh (Tree (x, xs)) = Tree (sinh x, sinh xs)
  cosh (Tree (x, xs)) = Tree (cosh x, cosh xs)
  tanh (Tree (x, xs)) = Tree (tanh x, tanh xs)
  asinh (Tree (x, xs)) = Tree (asinh x, asinh xs)
  acosh (Tree (x, xs)) = Tree (acosh x, acosh xs)
  atanh (Tree (x, xs)) = Tree (atanh x, atanh xs)


instance (Applicative m, Floating a) => Floating (Forest m a) where
  pi = Forest (pure pi)

  Forest xs ** Forest ys = Forest (liftA2 (**) xs ys)
  logBase (Forest xs) (Forest ys) = Forest (liftA2 logBase xs ys)

  exp (Forest xs) = Forest (exp <$> xs)
  log (Forest xs) = Forest (log <$> xs)
  sqrt (Forest xs) = Forest (sqrt <$> xs)
  sin (Forest xs) = Forest (sin <$> xs)
  cos (Forest xs) = Forest (cos <$> xs)
  tan (Forest xs) = Forest (tan <$> xs)
  asin (Forest xs) = Forest (asin <$> xs)
  acos (Forest xs) = Forest (acos <$> xs)
  atan (Forest xs) = Forest (atan <$> xs)
  sinh (Forest xs) = Forest (sinh <$> xs)
  cosh (Forest xs) = Forest (cosh <$> xs)
  tanh (Forest xs) = Forest (tanh <$> xs)
  asinh (Forest xs) = Forest (asinh <$> xs)
  acosh (Forest xs) = Forest (acosh <$> xs)
  atanh (Forest xs) = Forest (atanh <$> xs)



-- | Pull out a layer of monadic context from a `Forest`.
--
-- Not sure, but I think that the only inhabitants of this type can:
--
--  * return the original
--  * do this
--  * swap two `Tree` values
--  * some combination of the above
pullM :: Functor m => Forest m a -> m (Forest m a)
pullM (Forest xs) = snd . getTree <$> xs

-- | `pullM` and `extract`
pullMa :: Functor m => Forest m a -> m a
pullMa (Forest xs) = extract <$> xs

-- | Unfold a `Tree` from a seed value
unfoldTree   :: Functor m => (b -> (a, m b)) -> b -> Tree   m a
unfoldTree   f x = Tree   (Forest . fmap (unfoldTree   f) <$> f x)

-- | Unfold a `Forest` from a seed value
unfoldForest :: Functor m => (b -> m (a, b)) -> b -> Forest m a
unfoldForest f x = Forest (Tree .   fmap (unfoldForest f) <$> f x)

--  | Build a `Tree` using `Applicative` iteration
iterateTree :: Applicative m => (a -> m a) -> a -> m (Tree m a)
iterateTree f x = let y = f x in Tree <$> liftA2 (,) y (iterateForest f <$> y)

--  | Build a `Forest` using `Applicative` iteration
iterateForest :: Applicative m => (a -> m a) -> a -> Forest m a
iterateForest f x = Forest (iterateTree f x)





-- | Algebraic notes:
--
-- @
-- -- f' = (f / g) * g'
-- -- f' = (f / g) * ((g / f) * f')
-- -- f' = (*) ((/) f g) ((*) ((/) g f) f')
-- -- f' = (f `y` g) `x` ((g `y` f) `x` f')
-- @
--
-- @
-- f' x y f g = x (y f g) . x (y g f) $ f'
-- @
--
-- @
-- -- g' = (g / f) * f'
-- -- g' = (g / f) * ((f / g) * g')
-- -- g' = (g `y` f) `x` ((f `y` g) `x` g')
-- @
--
-- @
-- g' x y f g = x (y g f) . x (y f g) $ g'
-- @
--
-- @
-- f' = (f `y` g) `x` g'
-- g' = (g `y` h) `x` h'
-- h' = (h `y` f) `x` f'
-- @
--
-- If @`x`@ right-distributes over @`y`@:
--
-- @
--  f' = (f `y` g) `x` g' = (f `y` g') `x` (g `y` g')
--  g' = (g `y` h) `x` h' = (g `y` h') `x` (h `y` h')
--  h' = (h `y` f) `x` f' = (h `y` f') `x` (f `y` f')
--
--  f' = (f `y` g) `x` g' = (f `y` g) `x` ((g `y` h) `x` ((h `y` f) `x` f'))
--  g' = (g `y` h) `x` h' = (g `y` h) `x` ((h `y` f) `x` ((f `y` g) `x` g'))
--  h' = (h `y` f) `x` f' = (h `y` f) `x` ((f `y` g) `x` ((g `y` h) `x` h'))
--
--  f' = x (y f g) . x (y g f) $ f'
--  g' = x (y g f) . x (y f g) $ g'
--
--  f' = x (y f g) g' = x (y f g) . x (y g h) . x (y h f) $ f'
--  g' = x (y g h) h' = x (y g h) . x (y h f) . x (y f g) $ g'
--  h' = x (y h f) f' = x (y h f) . x (y f g) . x (y g h) $ h'
--
--  f' = x (y f g) g' = ((.) (x (y f g)) ((.) (x (y g h)) (x (y h f))) $ f'
--  g' = x (y g h) h' = x (y g h) . (x (y h f) . x (y f g)) $ g'
--  h' = x (y h f) f' = x (y h f) . (x (y f g) . x (y g h)) $ h'
-- @
--
--
-- @
--  (.) :: cat b c -> cat a b -> cat a c
--
--  (.) (x (y g h)) (x (y h f)) :: xygh b1 c1 -> xyhf a1 b1 -> ghf a1 c1
--  (.) (x (y h f)) (x (y f g)) :: xyhf b2 c2 -> xyfg a2 b2 -> hfg a2 c2
--  (.) (x (y f g)) (x (y g h)) :: xyfg b3 c3 -> xygh a3 b3 -> fgh a3 c3
--
--  (.) (x (y f g)) :: xyfg c1 d1 -> ghf a1 c1 -> C1 a1 d1
--  (.) (x (y g h)) :: xygh c2 d2 -> hfg a2 c2 -> C2 a2 d2
--  (.) (x (y h f)) :: xyhf c3 d3 -> fgh a3 c3 -> C2 a3 d3
-- @
--
--
-- So @x@ has to be at least a semigroupoid, to support composition
--
-- @
--    furthermore, it has to lift all the pairs to a common category
--    furthermore, it has to be funtorial, to allow preservation of internal properties
--  y :: `f -> `g -> `(y f g)
--  y :: `g -> `f -> `(y g f)
-- @
--
-- @
--  y :: `f -> `g -> `(y f g)
--  y :: `g -> `h -> `(y g h)
--  y :: `h -> `f -> `(y h f)
-- @
--
algebraicNotes :: ()
algebraicNotes = ()


-- | Algebraic examples:
--
-- @
--  La * Lb -> La
--
--  (La :*: Lb) a -> La a
--
--  (La -> (La || Lb)) -> (Lb -> (La || Lb)) -> (La -> La - Lb)
--
--  Suppose La <= Lb
-- @
--
-- @
--  A, B, A && B, A || B, A * B, A + B
--
--  Either A B
--  (A, B)
-- @
--
algebraicExamples :: ()
algebraicExamples = ()


-- Consider an arbitrary directed cycle of primitive languages.
--
-- For each @La@ such that @La -> Lb@, there exists a language @La'@ such that all the properties of @La@ hold in @La'@
--
-- (Because @La@'s properties leave the remaining unaffected?)
--
-- @
--  La' is defined as (La - Lb) * Lb'
--    Where (Lx - Ly) is the language formed by removing all properties of Ly from Lx
--    Where (Lx * Ly) is the cartesian product of Lx and Ly, formed of the pairs: (inhabitant of Ly, inhabitant of Lx)
-- @
--
--  All the properties of @La + Lb hold in La'@
--    because properties of La - Lb hold on the left and properties that intersect the two hold over the product.
--
--
--  What about expressability in a third language?
--    Great question.
--
--  What if the properties of the two languages somehow contradict or cancel each other out?
--    Well, at the moment, there's no logic attached so there's no logic to contradict.
--
--    Cancel each other out (possibly a.k.a. the union or intersection is uninhabited): No claims are made as to the inhabitants of the languages, so this doesn't seem to be a problem.
--
--  What can we say about non-empty, consistent sublanguages of a consistent language?
--    It'd be awesome, but I'm not sure it's possible, if we could guarantee distribution of properties.
--
--  I know it's possible in some cases, such as with
--
-- @
--  (Functor f, Monad m) => Tree m (f a) -> f (Tree m a)
-- @
--
-- But what about in general?
considerLanguageCycle :: ()
considerLanguageCycle = ()


-- | Thus we see that for languages based on @(->)@, aka application, every property seems to hold on either `Tree` or `Forest`:
--
-- - Because Tree is the combination of the Value language and the Action language
-- - Because ATree is the combination of the Semigroupoid language with the Category language (ATree doesn't have identity, AForest does, even though it contains ATree.)
--   * OR because @ATree@ is the product of @(Category - Identity)@ and @Category@..?
--   * So all associtive-requiring properties hold for both and all @associative+identity@-requiring properties only hold for @AForest@
--
--
-- If this construction works, then I believe it may be "self-holding", i.e. free:
-- The primitives used to express it are exactly the primitives needed to express it.
--
-- If this works and forms an internally consistent language,
-- then this effectively adds a primitive form of implementation-agnostic, decidable, recursion to Flock.
--
-- It also allows the simple addition of Categories, Application, Type hierarchies, etc. etc. etc.
--
-- Note: While I'm unsure whether any n-lang in the Flock core is sufficient to express itself, it's trivial to show that there's an (n+m)-lang that does (because of regularity).
--
-- Does this preserve: consistency, completeness, decidability, finiteness, haltingness, etc?
--
-- Well, if it's shown on a nice category-theoretic level, it doesn't really matter, no?
--
-- @
--  Everything will be preserved, [evil-laugh] XD
-- @
--
-- (That still cracks me up)
--
-- Natural extension of @A@. There is a function
--
-- @
--  f : A -> A',
--  f' :: A' -> A,
--  f' . f = id,
--  A' ~ A <=> f . f' = id
-- @
--
--  I wonder if this indeed forms a structure analogous to a factorization system for arbitrary categories?
propertyPreservation :: ()
propertyPreservation = ()


-- | More possibilities
--
-- @
-- f :: a -> a',
-- f' :: a' -> a,
-- f' . f = id,
-- Iso (a' ~ a) (f . f' = id)
-- @

-- @
-- f :: g a -> g' a',
-- f' :: g' a' -> g a,
-- f' . f = id
-- @
--
twoMoreAttempts :: ()
twoMoreAttempts = ()

-- | Summarize and notes:
--
-- @
-- F, G functors from C to D
-- n, natural transformation F -> G
--   nx :: forall (x :: C). F x -> G x
--   forall (f :: (x :: C) -> (y :: C)).
--     exists (ny :: F y -> G y).
--     ny . F (f :: x -> y) == G (f :: x -> y) . nx
-- @
--
-- @
-- Functor (f :: * -> *)
-- Functor (g :: * -> *)
-- @
--
-- @
-- f' = (f / g) * g'
-- f' = (f / g) * ((g / f) * f')
-- f' = (*) ((/) f g) ((*) ((/) g f) f')
-- f' = (f `y` g) `x` ((g `y` f) `x` f')
-- f' = x (y f g) (x (y g f) f')
--
-- g' = (g / f) * f'
-- g' = (g / f) * ((f / g) * g')
-- g' = (g `y` f) `x` ((f `y` g) `x` g')
-- @
--
naturalTransformationAlgebra :: ()
naturalTransformationAlgebra = ()

-- | Free/Cofree and algebra
--
-- @
-- newtype Free f a = Free { unfree :: Either a (f (Free f a))) }
--   Either a (f (Free f a))
--   (Either a :.: f :.: Free f)
-- Sum version of Tree f a
-- @
--
-- @
-- Cofree f a =  a :<  (f (Cofree f a))
--   Tree f a =  a (,) (f (Tree   f a))
-- @
--
-- @
-- Free f a = Pure a | Free (f (Free f a))
-- Free f a = Either a (f (Free f a))
-- Free f a = Either a (f (Either a (f (Free f a))))
-- Free f a = Either a (f -> (a, (Either a (f -> (a, )(Free f a)))))
-- Free (TT f a b) c = Either a (TT a b (Free (TT f a b) c))
-- Free (TT f a b) c = Either a (TT a b (Either a (TT a b (Free (TT f a b) c))))
-- @
--
-- @
-- Forest (Either a . f) a = Either a (f (a, Forest f a))
-- Forest f a = f (a, Forest f a)
-- Forest f a = f (Tree f a)
-- @
--
-- @
-- TT f a b = f a -> (a, b)
-- @
--
ttDefinition :: ()
ttDefinition = ()


-- | Free and Cofree instances:
--
-- @
-- newtype FreeT   f m a = FreeT   { runFreeT   :: m (FreeF f a (FreeT f m a)) }
--   newtype FreeT   f m a = m (Either a (f (FreeT f m a)))
--   newtype FreeT   f m a = m (Either a (f (m (Either a (f (FreeT f m a))))))
-- data FreeF   f a b = Pure a | Free (f b)
--   data FreeF   f a b = Either a (f b)
-- @
--
-- @
-- newtype CofreeT f w a = CofreeT { runCofreeT :: w (CofreeF f a (CofreeT f w a)) }
--   newtype CofreeT f w a = w (a, f (CofreeT f w a))
--   newtype CofreeT f w a = w (a, f (w (a, f (CofreeT f w a))))
-- data CofreeF f a b = a :< (f b)
--   data CofreeF f a b = (a, f b)
-- @
--
-- @
-- Functor f => Monad (Free f a) => MonadFree f (Free f) =>
--   wrap :: f (Free f a) -> Free f a
--   wrap x = Pure  (x :: f (Free f a))
--   wrap x = Right (x :: f (Free f a))
--
-- Monad f => Monad (Forest f a) =>
--   wrap :: f (Forest f a) -> Forest f a
--   wrap = (coerce :: (f (f (a, Forest f a)) -> f (a, Forest f a)) -> f (Forest f a) -> Forest f a) (join :: Monad f => f (f (a, Forest f a)) -> f (a, Forest f a))
-- @
--
freeAndCofree :: ()
freeAndCofree = ()



-- | Lift an `Enum` to a `Tree` type where the outermost is first?
--
-- Hmm.. I know that we can't use the internal monadic structure of `Tree` since we know nothing about it.
--
-- What would we like to do with this? well, it might be nice to add labeling to a `Tree` using `Enum`
--
-- @
--  instance Enum a => Enum (Tree m a) where
--
--  -- The functions below are for `Forest`, since we probably can't do `fromEnum`
--
--  -- | the successor of a value. For numeric types, succ adds 1.
--  succM :: a -> a
--
--  -- | the predecessor of a value. For numeric types, pred subtracts 1.
--  predM :: a -> a
--
--  -- | Convert from an Int.
--  toEnumM :: Int -> a
--
--  -- | Convert to an Int. It is implementation-dependent what fromEnum returns when applied to a value that is too large to fit in an Int.
--  fromEnumM :: a -> Int
--
--  -- | Used in Haskell's translation of [n..].
--  enumFromM :: a -> [a]
--
--  -- | Used in Haskell's translation of [n,n'..].
--  enumFromThenM :: a -> a -> [a]
--
--  -- | Used in Haskell's translation of [n..m].
--  enumFromToM :: a -> a -> [a]
--
--  -- | Used in Haskell's translation of [n,n'..m].
--  enumFromThenToM :: a -> a -> a -> [a]
-- @
--
ideaInstanceEnum :: ()
ideaInstanceEnum = ()



