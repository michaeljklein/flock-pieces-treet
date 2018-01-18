{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Monad.Trans.TreeT where


import Control.Applicative (Alternative(..), liftA2)
import Control.Arrow (Arrow(..))
import Control.Category (Category(..), (>>>))
import Control.Comonad (Comonad(..), ComonadApply(..))
import Control.Comonad.Trans.Class (ComonadTrans(..))
import Control.Monad hiding (fail)
import Data.Biapplicative hiding (first, second)
import Data.Coerce (Coercible, coerce)
import Data.Functor.Classes (Eq1(..), Ord1(..))
import Data.Groupoid (Groupoid(..))
import Data.Monoid ((<>))
import Data.Profunctor (Profunctor(..), Closed(..), Choice(..), Strong(..))
import Data.Semigroup hiding ((<>))
import Data.Semigroupoid (Semigroupoid(..))
import GHC.Generics (Generic)
import GHC.TypeLits (TypeError, ErrorMessage(Text))
import Prelude hiding (fail, id, (.))
import Unsafe.Coerce (unsafeCoerce)


-- I'm calling this out of scope:
--
-- import Pointfree
-- pfRec :: String -> [String] -> String -> [String]
-- pfRec fname args expr = minsBy cmpLength . (>>= pointfree) . fmap (\_ -> unwords $ fname : args ++ ["=", expr]) . permutations $ args

-- | Compare length of lists, without `Int` or `Eq`
cmpLength :: [a] -> [b] -> Ordering
cmpLength (_:xs) (_:ys) = cmpLength xs ys
cmpLength (  []) (_:_ ) = LT
cmpLength (_:_ ) (  []) = GT
cmpLength (  _ ) (  _ ) = EQ

-- | Minimums by:
minsBy :: (a -> a -> Ordering) -> [a] -> [a]
minsBy _ []     = []
minsBy f (x:xs) = looop x [x] xs
  where
    looop n ys (z:zs) = case f n z of
                         LT -> looop n    ys  zs
                         EQ -> looop n (z:ys) zs
                         GT -> looop z [z]    zs
    looop _ ys  _     = ys


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

-- Consider an arbitrary directed cycle of primitive languages
--
-- For each La such that La -> Lb, there exists a language La' such that
--  All the properties of La hold in La'
--    because La's properties leave the remaining unaffected?
--  La' is defined as (La - Lb) * Lb'
--    Where (Lx - Ly) is the language formed by removing all properties of Ly from Lx
--    Where (Lx * Ly) is the cartesian product of Lx and Ly, formed of the pairs: (inhabitant of Ly, inhabitant of Lx)
--  All the properties of La + Lb hold in La'
--    because properties of La - Lb hold on the left and properties that intersect the two hold over the product
--  What about expressability in a third language?
--    Great question
--  What if the properties of the two languages somehow contradict or cancel each other out?
--    Well, at the moment, there's no logic attached so there's no logic to contradict
--    Cancel each other out (possibly a.k.a. the union or intersection is uninhabited): No claims are made as to the inhabitants of the languages, so this doesn't seem to be a problem
--  What can we say about non-empty, consistent sublanguages of a consistent language?
--    It'd be awesome, but I'm not sure it's possible, if we could guarantee distribution of properties
--      I know it's possible in some cases, such as with (Functor f, Monad m) => Tree m (f a) -> f (Tree m a), but what about in general?
--
--      It looks like this might work because
--
--
--
-- Thus we see that for languages based on (->), aka application, every property seems to hold on either Tree or Forest,
--  Because Tree is the combination of the Value language and the Action language
--  Because ATree is the combination of the Semigroupoid language with the Category language (ATree doesn't have identity, AForest does, even though it contains ATree.)
--    OR because ATree is the product of (Category - Identity) and Category
--    So all associtive-requiring properties hold for both and all associative+identity-requiring properties only hold for AForest
--
--
-- If this construction works, then I believe it may be self-holding: The primitives used to express it are exactly the primitives needed to express it
--
-- If this works and forms an internally consistent language, then this effectively adds a primitive form of implementation-agnostic, decidable, recursion to Flock.
--  It also allows the simple addition of Categories, Application, Type hierarchies, etc. etc. etc.
--  Note: While I'm unsure whether any n-lang in the Flock core is sufficient to express itself, it's trivial to show that there's an (n+m)-lang that does (because of regularity)
--
-- Does this preserve: consistency, completeness, decidability, finiteness, haltingness, etc?
-- Well, if it's shown on a nice category-theoretic level, it doesn't really matter, no?
-- Everything will be preserved, [evil-laugh] XD


-- Natural extension of A. There is a function f : A -> A', f' :: A' -> A, f' . f = id, A' ~ A <=> f . f' = id
--  huh, I wonder if this indeed forms a structure analogous to a factorization system for arbitrary categories?


{-
f :: a -> a', f' :: a' -> a, f' . f = id, Iso (a' ~ a) (f . f' = id)

f :: g a -> g' a', f' :: g' a' -> g a, f' . f = id

F, G functors from C to D
n, natural transformation F -> G
  nx :: forall (x :: C). F x -> G x
  forall (f :: (x :: C) -> (y :: C)).
    exists (ny :: F y -> G y).
    ny . F (f :: x -> y) == G (f :: x -> y) . nx

Functor (f :: * -> *)
Functor (g :: * -> *)


f' = (f / g) * g'
f' = (f / g) * ((g / f) * f')
f' = (*) ((/) f g) ((*) ((/) g f) f')
f' = (f `y` g) `x` ((g `y` f) `x` f')
f' = x (y f g) (x (y g f) f')

g' = (g / f) * f'
g' = (g / f) * ((f / g) * g')
g' = (g `y` f) `x` ((f `y` g) `x` g')


newtype Free f a = Free { unfree :: Either a (f (Free f a))) }
  Either a (f (Free f a))
  (Either a :.: f :.: Free f)
Sum version of Tree f a

Cofree f a =  a :<  (f (Cofree f a))
  Tree f a =  a (,) (f (Tree   f a))

Free f a = Pure a | Free (f (Free f a))
Free f a = Either a (f (Free f a))
Free f a = Either a (f (Either a (f (Free f a))))
Free f a = Either a (f -> (a, (Either a (f -> (a, )(Free f a)))))
Free (TT f a b) c = Either a (TT a b (Free (TT f a b) c))
Free (TT f a b) c = Either a (TT a b (Either a (TT a b (Free (TT f a b) c))))


Forest (Either a . f) a = Either a (f (a, Forest f a))
Forest f a = f (a, Forest f a)
Forest f a = f (Tree f a)

TT f a b = f a -> (a, b)

Functor f => Monad (Free f a) => MonadFree f (Free f) =>
  wrap :: f (Free f a) -> Free f a
  wrap x = Pure  (x :: f (Free f a))
  wrap x = Right (x :: f (Free f a))

Monad f => Monad (Forest f a) =>
  wrap :: f (Forest f a) -> Forest f a
  wrap = (coerce :: (f (f (a, Forest f a)) -> f (a, Forest f a)) -> f (Forest f a) -> Forest f a) (join :: Monad f => f (f (a, Forest f a)) -> f (a, Forest f a))

newtype FreeT   f m a = FreeT   { runFreeT   :: m (FreeF f a (FreeT f m a)) }
  newtype FreeT   f m a = m (Either a (f (FreeT f m a)))
  newtype FreeT   f m a = m (Either a (f (m (Either a (f (FreeT f m a))))))
data FreeF   f a b = Pure a | Free (f b)
  data FreeF   f a b = Either a (f b)

newtype CofreeT f w a = CofreeT { runCofreeT :: w (CofreeF f a (CofreeT f w a)) }
  newtype CofreeT f w a = w (a, f (CofreeT f w a))
  newtype CofreeT f w a = w (a, f (w (a, f (CofreeT f w a))))
data CofreeF f a b = a :< (f b)
  data CofreeF f a b = (a, f b)
-}


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

-- instance Monad m => Monad (Forest m) where
--   return :: a -> Forest m a
--   return x = Forest (return (return x))

--   (>>=) :: Forest m a -> (a -> Forest m a) -> Forest m a
--   Forest xs >>= f = Forest (join (getForest . f . extract <$> xs))


instance Functor m => Comonad (Tree m) where
  extract :: Tree m a -> a
  extract (Tree (x, _)) = x

  duplicate :: Tree m a -> Tree m (Tree m a)
  duplicate (Tree (x, Forest xs)) = Tree (Tree (x, Forest xs), Forest (duplicate <$> xs))

instance Applicative m => ComonadApply (Tree m) where
  (<@>) :: Tree m (a -> b) -> Tree m a -> Tree m b
  Tree (f, fs) <@> Tree (x, xs) = Tree (f x, fs <*> xs)

-- instance MonadTrans Forest where
--   lift :: Monad m => m a -> Forest m a
--   lift = Forest . liftTree
-- -- lift . return = return
-- -- lift (m >>= f) = lift m >>= (lift . f)

-- instance MonadIO m => MonadIO (Forest m) where
--   liftIO :: IO a -> Forest m a
--   liftIO = lift . liftIO
-- -- liftIO . return = return
-- -- liftIO (m >>= f) = liftIO m >>= (liftIO . f)

-- instance MonadState s m => MonadState s (Forest m) where
--   get = lift get
--   put = lift . put
--   state = lift . state

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


-- -- | `Tree` is not a monad transformer, but @`Tree` . m@ is, for @`Monad` m@
-- liftTree :: Monad m => m a -> m (Tree m a)
-- liftTree x = Tree <$> fmap (, lift x) x

-- | Push a monadic context into a `Forest` by binding it and unwrapping the forest.
--
-- It should be equivalent to:
--
-- @
--  Forest . join . fmap getForest
--  Forest .        (>>= getForest)
-- @
-- instance MonadFree f m where
--   wrap :: m (Forest m a) -> Forest m a
--   wrap fs = Forest (fs >>= getForest)

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

pullMa :: Functor m => Forest m a -> m a
pullMa (Forest xs) = extract <$> xs

unfoldTree   :: Functor m => (b -> (a, m b)) -> b -> Tree   m a
unfoldTree   f x = Tree   (Forest . fmap (unfoldTree   f) <$> f x)

unfoldForest :: Functor m => (b -> m (a, b)) -> b -> Forest m a
unfoldForest f x = Forest (Tree .   fmap (unfoldForest f) <$> f x)


iterateTree :: Applicative m => (a -> m a) -> a -> m (Tree m a)
iterateTree f x = let y = f x in Tree <$> liftA2 (,) y (iterateForest f <$> y)

iterateForest :: Applicative m => (a -> m a) -> a -> Forest m a
iterateForest f x = Forest (iterateTree f x)


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


-- instance PrimMonad m => PrimMonad (Forest m) where
--   type PrimState (Forest m) = PrimState m

--   primitive = lift . primitive


-- instance PrimBase m => PrimBase (Forest m) where
--   internal = internal . pullMa


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


-- -- | Lift an `Enum` to a `Tree` type where the outermost is first?
-- -- Hmm.. I know that we can't use the internal monadic structure of `Tree` since we know nothing about it.
-- --
-- -- What would we like to do with this? well, it might be nice to add labeling to a `Tree` using `Enum`
-- instance Enum a => Enum (Tree m a) where
--
-- -- The functions below are for `Forest`, since we probably can't do `fromEnum`
--
-- -- | the successor of a value. For numeric types, succ adds 1.
-- succM :: a -> a
--
-- -- | the predecessor of a value. For numeric types, pred subtracts 1.
-- predM :: a -> a
--
-- -- | Convert from an Int.
-- toEnumM :: Int -> a
--
-- -- | Convert to an Int. It is implementation-dependent what fromEnum returns when applied to a value that is too large to fit in an Int.
-- fromEnumM :: a -> Int
--
-- -- | Used in Haskell's translation of [n..].
-- enumFromM :: a -> [a]
--
-- -- | Used in Haskell's translation of [n,n'..].
-- enumFromThenM :: a -> a -> [a]
--
-- -- | Used in Haskell's translation of [n..m].
-- enumFromToM :: a -> a -> [a]
--
-- -- | Used in Haskell's translation of [n,n'..m].
-- enumFromThenToM :: a -> a -> a -> [a]



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


-- | Does this work? What if @m@ is a bifunctor?
--
-- newtype TreeArrow a b c = TreeArrow { runTreeArrow :: Tree (a b) c) }         (c,  Forest (a b) c)
-- newtype ForestArrow a b c = ForestArrow { runForestArrow :: Forest (a b) c }  a b (Tree   (a b) c)


-- newtype Tree   m a = Tree   { getTree   :: (a, Forest m a) } deriving (Generic)
-- newtype Forest m a = Forest { getForest :: m (Tree m a) } deriving (Generic)

-- instance Category a => Category (TreeArrow a b c) where
--   (.) :: TreeArrow b c -> TreeArrow a b -> TreeArrow a c
--   Tree (cat b) c -> Tree (cat a) b -> Tree (cat a) c
--   (c, Forest (cat b) c) -> (b, Forest (cat a) b) -> (c, Forest (cat a) c)
--   (c, b -> (Tree (b ->) c)) -> (b, a -> (Tree (a ->) b)) -> (c, a -> (Tree (a ->) c))
--   (c, b -> (c, Forest (b ->) c)) -> (b, a -> (b, Forest (a ->) b)) -> (c, a -> (c, Forest (a ->) c))


--   (x1, fx1) (y1, fy1)
--   (x1 :: c,
--   \(z1 :: a) ->
--     (x2 :: c, fx2 :: b -> (c, Forest (b ->) c)) = fx1 y1 :: (c, Forest (b ->) c)
--     (y2 :: b, fy2 :: a -> (b, Forest (a ->) b)) = fy1 z1 :: (b, Forest (a ->) b)
--     (x2 :: c,
--     \(z2 :: a) ->
--       (x3 :: c, fx3 :: b -> (c, Forest (b ->) c)) = fx2 y2 :: (c, Forest (b ->) c)
--       (y3 :: b, fy3 :: a -> (b, Forest (a ->) b)) = fy2 z2 :: (b, Forest (a ->) b)
--       (x3 :: c,
--       \(z3 :: a) ->
--         ..

-- | Compose two `Tree`s
comp :: Tree ((->) b) c -> Tree ((->) a) b -> Tree ((->) a) c
comp (Tree (x1, Forest fx1)) (Tree (y1, Forest fy1)) = Tree (x1, Forest (\z1 -> comp (fx1 y1) (fy1 z1)))

-- | `coerce`
getTree2 :: (Tree ma a -> Tree mb b -> Tree mc c) -> (a, Forest ma a) -> (b, Forest mb b) -> (c, Forest mc c)
getTree2 = coerce


-- | `unsafeCoerce` is used for now, since the following error appears:
--
-- @
--  • Couldn't match representation of type ‘t a (c, Forest (t a) c)’
--                             with that of ‘t a (Tree (t a) c)’
--      arising from a use of ‘coerce’
--    NB: We cannot know what roles the parameters to ‘t a’ have;
--      we must assume that the role is nominal
-- @
--
-- This is safe by the following:
--
-- @
--  (arr coerce .)   :: (Arrow t, Coercible b c) => t a b -> t a c -- initial definition
--    = (coerce .)   :: (Arrow t, Coercible b c) => t a b -> t a c -- arr id = id
--    = coerce       :: (Arrow t, Coercible b c) => t a b -> t a c -- (id .) = id
-- @
arrCoerce :: (Arrow a, Coercible c d) => a b c -> a b d
arrCoerce = unsafeCoerce



-- | `coerce` more strangely doesn't work here either. weird
goal' :: Arrow t => ATree t b c -> ATree t a b -> ATree t a c
goal' (ATree f) (ATree g) = ATree (goal f g)

-- | Goal function
goal :: Arrow t => Tree (t b) c -> Tree (t a) b -> Tree (t a) c
goal = trans1 goal1

-- | `coerce`
trans1 :: ((a, Forest ma a) -> (b, Forest mb b) -> (c, Forest mc c)) -> Tree ma a -> Tree mb b -> Tree mc c
trans1 = coerce

-- | @`trans2` `goal2`@
goal1 :: Arrow t => (c, Forest (t b) c) -> (b, Forest (t a) b) -> (c, Forest (t a) c)
goal1 = trans2 goal2

-- | `coerce`
trans2 :: Arrow t => ((c, t b (Tree (t b) c)) -> (b, t a (Tree (t a) b)) -> (c, t a (Tree (t a) c))) -> (c, Forest (t b) c) -> (b, Forest (t a) b) -> (c, Forest (t a) c)
trans2 = coerce

-- | Second goal function
--
-- @
--  goal2 (x, fx) (y, fy) = (x, arr (uncurry goal) . (fx . arr (const y) &&& fy))
-- @
--
goal2 :: Arrow t => (c, t b (Tree (t b) c)) -> (b, t a (Tree (t a) b)) -> (c, t a (Tree (t a) c))
goal2 (x, fx) (y, fy) = (x, fx . arr (const y) &&& fy >>> arr (uncurry goal))


-- | Coerce doesn't work here, which is too bad
laog' :: Arrow t => AForest t b c -> AForest t a b -> AForest t a c
laog' (AForest f) (AForest g) = AForest (laog f g)

-- | @`snart1` `laog1`@
laog :: Arrow t => Forest (t b) c -> Forest (t a) b -> Forest (t a) c
laog = snart1 laog1

-- | `coerce`
snart1 :: Arrow t => (t b (Tree (t b) c) -> t a (Tree (t a) b) -> t a (Tree (t a) c)) -> Forest (t b) c -> Forest (t a) b -> Forest (t a) c
snart1 = coerce

-- | @`snart2` `laog2`@
laog1 :: Arrow t => t b (Tree (t b) c) -> t a (Tree (t a) b) -> t a (Tree (t a) c)
laog1 = snart2 laog2

-- | By the logic of `arrCoerce`, this use of `unsafeCoerce` is safe
snart2 :: Arrow t => (t b (c, Forest (t b) c) -> t a (b, Forest (t a) b) -> t a (c, Forest (t a) c)) -> t b (Tree (t b) c) -> t a (Tree (t a) b) -> t a (Tree (t a) c)
snart2 = unsafeCoerce

-- | Opposite of `goal2`
laog2 :: Arrow t => t b (c, Forest (t b) c) -> t a (b, Forest (t a) b) -> t a (c, Forest (t a) c)
laog2 fx fy = second (arr (uncurry laog)) . arr assoc . first fx . fy



-- | Wow, coerce doesn't work here. I had to use the `AForest` constructor instead
--
-- Notes:
--
-- So, technically, it appears that `Tree` is only a category when we have a left-identity for @`Arrow a`@
--
-- We can however do stuff like:
--
-- @
--  a -> Tree (t a) a
--  t a (Tree (t a) a
-- @
--
-- @
-- idTree :: Arrow t => Tree (t a) a
-- idTree1 :: Arrow t => (a, Forest (t a) a)
-- @
--
idForest' :: Arrow t => AForest t a a
idForest' = AForest idForest

-- | See `idForest`
idForest :: Arrow t => Forest (t a) a
idForest = transIdForest1 idForest1

-- | `coerce`
transIdForest1 :: Arrow t => t a (Tree (t a) a) -> Forest (t a) a
transIdForest1 = coerce

-- | @`transIdForest2` `idForest2`@
idForest1 :: Arrow t => t a (Tree (t a) a)
idForest1 = transIdForest2 idForest2

-- | `arrCoerce`
transIdForest2 :: Arrow t => t a (a, Forest (t a) a) -> t a (Tree (t a) a)
transIdForest2 = arrCoerce

-- | Coerced all the way up to `idForest`
idForest2 :: Arrow t => t a (a, Forest (t a) a)
idForest2 = id &&& (arr snd . idForest2)

-- | Like `Tree`, but the arguments are applied differently
newtype ATree   t a b = ATree   { getATree   :: Tree   (t a) b } deriving (Generic)

-- | See `AForest`
newtype AForest t a b = AForest { getAForest :: Forest (t a) b } deriving (Generic)

-- | @`o` = `laog'`
instance Arrow t => Semigroupoid (AForest t) where
  o :: AForest t b c -> AForest t a b -> AForest t a c
  o = laog'


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

-- | @`inv` = `forestInv`@
instance (Arrow t, Groupoid t) => Groupoid (AForest t) where
  inv :: AForest t a b -> AForest t b a
  inv = forestInv

-- | @`(.)` = `laog'`@, @`id` = `idForest'`@
instance Arrow t => Category (AForest t) where
  (.) :: AForest t b c -> AForest t a b -> AForest t a c
  (.) = laog'

  id :: AForest t a a
  id = idForest'

-- | @`o` = `goal'`@
instance Arrow t => Semigroupoid (ATree t) where
  o :: ATree t b c -> ATree t a b -> ATree t a c
  o = goal'



instance Functor (t a) => Functor (ATree t a) where
  fmap :: (b -> c) -> ATree t a b -> ATree t a c
  fmap f (ATree ts) = ATree (fmap f ts)

instance Functor (t a) => Functor (AForest t a) where
  fmap :: (b -> c) -> AForest t a b -> AForest t a c
  fmap f (AForest fs) = AForest (fmap f fs)


instance Bifunctor t => Bifunctor (ATree t) where
  bimap :: (a -> b) -> (c -> d) -> ATree t a c -> ATree t b d
  bimap f g (ATree (Tree (x, xs))) = ATree (Tree (g x, getAForest (bimap f g (AForest xs))))

instance Bifunctor t => Bifunctor (AForest t) where
  bimap :: (a -> b) -> (c -> d) -> AForest t a c -> AForest t b d
  bimap f g (AForest (Forest xs)) = AForest (Forest (bimap f (getATree . bimap f g . ATree) xs))


instance Biapplicative t => Biapplicative (ATree t) where
  bipure x y = ATree (Tree (y, getAForest (bipure x y)))

  ATree (Tree (f, fs)) <<*>> ATree (Tree (x, xs)) = ATree (Tree (f x, getAForest (AForest fs <<*>> AForest xs)))

-- | This also looks a lot like distribution.. (`undefined`)
instance Biapplicative t => Biapplicative (AForest t) where
  bipure x y = AForest (Forest (bipure x (getATree (bipure x y))))

  AForest (Forest fs) <<*>> AForest (Forest xs) = AForest (Forest ((undefined fs) <<*>> xs))
        -- _ :: t (a -> b) (Tree (t (a -> b)) (c -> d)) -> t (a -> b) (Tree (t a) c -> Tree (t b) d)


-- Data.Bifoldable
-- instance Bifoldable t => Bifoldable (ATree t) where
--   bifoldr :: (a -> c -> c) -> (b -> c -> c) -> c -> t a b -> c
--   bifoldr :: (a -> c -> c) -> (b -> c -> c) -> c -> ATree t a b -> c
--   bifoldr :: (a -> c -> c) -> (b -> c -> c) -> c -> Tree (t a) b -> c

-- This makes me think that Forest (t a) b ~ Forest (Forest t a) b, which would be amazeballs
-- Maybe something similar, like the `wanted` functions?
--
-- instance Bifoldable t => Bifoldable (AForest t) where
--   bifoldr :: (a -> c -> c) -> (b -> c -> c) -> c -> t a b -> c
--   bifoldr :: (a -> c -> c) -> (b -> c -> c) -> c -> Forest (t a) b -> c


-- Data.Bitraversable
-- class (Bifunctor t, Bifoldable t) => Bitraversable t
--   bitraverse :: Applicative f => (a -> f c) -> (b -> f d) -> t a b -> f (t c d)


-- Data.Bifunctor.Functor
-- type (:->) p q = forall a b. p a b -> q a b
--
-- class BifunctorFunctor t where
--   bifmap :: (p :-> q) -> t p :-> t q


instance Profunctor t => Profunctor (ATree t) where
  dimap :: (a -> b) -> (c -> d) -> ATree t b c -> ATree t a d
  dimap f g (ATree (Tree (x, xs))) = ATree (Tree (g x, getAForest (dimap f g (AForest xs))))

instance Profunctor t => Profunctor (AForest t) where
  dimap :: (a -> b) -> (c -> d) -> AForest t b c -> AForest t a d
  dimap f g (AForest (Forest xs)) = AForest (Forest (dimap f (getATree . dimap f g . ATree) xs))


-- | This looks a lot like distribution
instance Strong t => Strong (AForest t) where
  first'  :: AForest t a b -> AForest t (a, c) (b, c)
  first' (AForest (Forest fs)) = AForest (Forest (rmap (Tree . fmap (getAForest . first' . AForest) . sndIn . first getTree) (first' fs)))

  second' :: AForest t a b -> AForest t (c, a) (c, b)
  second' (AForest (Forest fs)) = AForest (Forest $ rmap (Tree . fmap (getAForest . second' . AForest) . unassoc . second getTree) $ (second' fs))

-- | Re-associate a tuple
sndIn :: ((a, b), c) -> ((a, c), b)
sndIn ((x, y), z) = ((x, z), y)



instance Choice t => Choice (ATree t) where
  left' :: ATree t a b -> ATree t (Either a c) (Either b c)
  left' (ATree (Tree (x, xs))) = ATree (Tree (Left x, getAForest (left' (AForest xs))))
  -- left' :: Tree (t a) b -> Tree (t (Either a c)) (Either b c)
  -- left' :: (b, Forest (t a) b) -> (Either b c, Forest (t (Either a c)) (Either b c))

  right' :: ATree t a b -> ATree t (Either c a) (Either c b)
  right' (ATree (Tree (x, xs))) = ATree (Tree (Right x, getAForest (right' (AForest xs))))
  -- right' :: Tree (t a) b -> Tree (t (Either c a)) (Either c b)
  -- right' :: (b, Forest (t a) b) -> (Either c b, Forest (t a) b)

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


-- class (Choice p, Strong p) => Traversing p where
--   Note: Definitions in terms of wander are much more efficient!
--
--   Minimal complete definition: wander | traverse'
--
--   traverse' :: Traversable f => p a b -> p (f a) (f b) Source #
--
--   wander :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> p a b -> p s t


-- class (Traversing p, Closed p) => Mapping p where
--   map' :: Functor f => p a b -> p (f a) (f b)


-- class Profunctor p => Costrong p where
--   Minimal complete definition: unfirst | unsecond
--
--   unfirst  :: p (a, d) (b, d) -> p a b
--   unsecond :: p (d, a) (d, b) -> p a b


-- class Profunctor p => Cochoice p where
--   Minimal complete definition: unleft | unright
--
--   unleft  :: p (Either a d) (Either b d) -> p a b
--   unright :: p (Either d a) (Either d b) -> p a b








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


-- | I'm pretty surprised that this isn't in base
assoc :: ((a, b), c) -> (a, (b, c))
assoc ~((x, y), z) = (x, (y, z))

-- | Inverse of `assoc`
unassoc :: (a, (b, c)) -> ((a, b), c)
unassoc ~(x, (y, z)) = ((x, y), z)


-- | Lift functions, inside of a `Tree`, into `Arrow`s
--
-- Scratch notes:
--
-- @
-- arr :: Arrow a => (b -> c) -> a b c
-- arr . const :: Arrow a => c -> a b c
--
-- arr Tree    :: Arrow a => a (c, Forest (a b) c) (Tree (a b) c)
-- arr getTree :: Arrow a => a (Tree (a b) c) (c, Forest (a b) c)
--
-- arr Forest    :: Arrow a => a (a b (Tree (a b) c)) (Forest (a b) c)
-- arr getForest :: Arrow a => a (Forest (a b) c) (a b (Tree (a b) c))
-- @
--
-- Wow, this just blew my mind. If we have cat be an arrow, then the pair operations that I use above are already given!!
--
-- @
-- TreeArrow (Tree (f, fs)) . TreeArrow (Tree (g, gs)) = TreeArrow (Tree (f, fs . gs))
-- @
--
-- @
-- compf :: Forest ((->) b) c -> Forest ((->) a) b -> Forest ((->) a) c
-- compf :: (b -> Tree ((->) b) c) -> (a -> Tree ((->) a) b) -> (c -> Tree ((->) a) c)
-- compf :: (b -> (c, Forest ((->) b) c)) -> (a -> (b, Forest ((->) a) b)) -> (c -> (c, Forest ((->) a) c))
-- @
--
--
-- I'm willing to bet that Tree is analogous to True (as it's inhabited) and Forest is analogous to False (as it's not, yet):
--
-- @
--   Tree && Tree forms a Tree:   (a & b -> c) -> (Tree m a & Tree m b) -> Tree m c
--   Tree || Forest forms a Tree: (a | b -> c) -> (Tree m a | Forest m b) -> Tree m c
--   Forest || Forest forms a Tree: (a | b -> c) -> (Forest m a | Forest m b) -> Forest m c
-- @
--
-- Ohhh, can we also lift inside? Duh, as long as m is applicative!
--
-- @
--   (a | b -> c) -> Tree m (a | b) -> Tree m c
-- @
--
-- Can we convert a comonad to a monad?
--
-- @
--   (w a -> a) looks like a monad to me, in fact, it appears to be: Forest (CoKleisi a) b,
--     Cokleisli { runCokleisli :: w a -> b }
--     Instances: .. Monad (Cokleisli w a)
-- @
--
-- Can we convert a monad to a comonad?
--
-- @
--   (a, a -> m a) looks like a comonad to me, in fact it appears to be: Tree State a
-- @
--
ss :: Arrow a => Tree ((->) b) c -> Tree (a b) c
ss (Tree (x, xs)) = Tree (x, tt xs)

-- | `Forest` counterpart to `ss`
tt :: Arrow a => Forest ((->) b) c -> Forest (a b) c
tt (Forest xs) = Forest (arr ss . arr xs)



