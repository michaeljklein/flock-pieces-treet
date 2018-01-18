{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Arrow.Tree where

import Control.Arrow (Arrow(..))
import Control.Category (Category(..), (>>>))
import Control.Monad hiding (fail)
import Control.Monad.Trans.TreeT (Tree(..), Forest(..))
import Data.Biapplicative hiding (first, second)
import Data.Coerce (Coercible, coerce)
import Data.Groupoid (Groupoid(..))
import Data.Profunctor (Profunctor(..), Closed(..), Choice(..), Strong(..))
import Data.Semigroupoid (Semigroupoid(..))
import GHC.Generics (Generic, Generic1)
import GHC.TypeLits (TypeError, ErrorMessage(Text))
import Prelude hiding (fail, id, (.))
import Unsafe.Coerce (unsafeCoerce)


-- | Like `Tree`, but the arguments are applied differently, to allow it to be an `Arrow`
newtype ATree   t a b = ATree   { getATree   :: Tree   (t a) b } deriving (Generic, Generic1)

-- | See `AForest`
newtype AForest t a b = AForest { getAForest :: Forest (t a) b } deriving (Generic, Generic1)

-- | @`o` = `laog'`
instance Arrow t => Semigroupoid (AForest t) where
  o :: AForest t b c -> AForest t a b -> AForest t a c
  o = laog'



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

-- | Notes on Data.Bifoldable, Data.Bitraversable, etc:
--
-- @
-- Data.Bifoldable
-- instance Bifoldable t => Bifoldable (ATree t) where
--   bifoldr :: (a -> c -> c) -> (b -> c -> c) -> c -> t a b -> c
--   bifoldr :: (a -> c -> c) -> (b -> c -> c) -> c -> ATree t a b -> c
--   bifoldr :: (a -> c -> c) -> (b -> c -> c) -> c -> Tree (t a) b -> c
--
-- This makes me think that Forest (t a) b ~ Forest (Forest t a) b, which would be amazeballs
-- Maybe something similar, like the `wanted` functions?
--
-- instance Bifoldable t => Bifoldable (AForest t) where
--   bifoldr :: (a -> c -> c) -> (b -> c -> c) -> c -> t a b -> c
--   bifoldr :: (a -> c -> c) -> (b -> c -> c) -> c -> Forest (t a) b -> c
-- @
--
-- @
-- Data.Bitraversable
-- class (Bifunctor t, Bifoldable t) => Bitraversable t
--   bitraverse :: Applicative f => (a -> f c) -> (b -> f d) -> t a b -> f (t c d)
-- @
--
-- @
-- Data.Bifunctor.Functor
-- type (:->) p q = forall a b. p a b -> q a b
--
-- class BifunctorFunctor t where
--   bifmap :: (p :-> q) -> t p :-> t q
-- @
--
bifoldableNotes :: ()
bifoldableNotes = ()


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



-- | Re-associate a tuple
sndIn :: ((a, b), c) -> ((a, c), b)
sndIn ((x, y), z) = ((x, z), y)

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
treeArr :: Arrow a => Tree ((->) b) c -> Tree (a b) c
treeArr (Tree (x, xs)) = Tree (x, forestArr xs)

-- | `Forest` counterpart to `treeArr`
forestArr :: Arrow a => Forest ((->) b) c -> Forest (a b) c
forestArr (Forest xs) = Forest (arr treeArr . arr xs)


