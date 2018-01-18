{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Bidistributable where

import Control.Applicative (liftA2)
import Control.Category (Category(..))
import Control.Comonad (Comonad(..))
import Data.Biapplicative (Biapplicative(..), biliftA2)
import Data.Bifunctor (Bifunctor(..))
import Data.Either (isLeft, isRight)
import Data.Functor.Classes (Eq2(..), Ord2(..), Show2(..), eq2, compare2, showsPrec2)
import Data.Maybe (fromJust, listToMaybe, catMaybes)
import Data.Monoid ((<>))
import Prelude hiding (unlines, lines, id, (.))
import qualified Prelude as P (concat)


-- | Distribute over a `Bifunctor`
class Bifunctor p => Bidistributable p f where
  -- | Later called "push" and or "push2"
  bidistribute :: f (p a b) -> f (p (f a) (f b))

instance Bidistributable Either [] where
  bidistribute :: [Either a b] -> [Either [a] [b]]
  bidistribute (Left  x : xs) = uncurry (:)        . bimap              (Left  . (x :) . fmap (\(~(Left  y)) -> y)) bidistribute . Prelude.span isLeft  $ xs
  bidistribute (Right x : xs) = uncurry (flip (:)) . bimap bidistribute (Right . (x :) . fmap (\(~(Right y)) -> y)) .              Prelude.span isRight $ xs
  bidistribute  _             = []


-- | This is a fun data type, later called.. a "Chain"
newtype Rope p a b = Rope { pullRope :: p a (Rope p b a) }

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



class Swap p where
  swap :: p a b -> p b a

instance Swap (,) where
  swap ~(x, y) = (y, x)

instance Swap Either where
  swap  (Left  x) = Right x
  swap ~(Right x) = Left  x


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






-- | `expand` and `contract`
--
-- @
-- dist :: f (p a b) -> RopeT m p (f a) (f b)
--
-- dist :: f (Either a b) -> RopeT Maybe (,) (f a) (f b)
-- @
--
class Functor f => Biexpandcontract (q :: * -> * -> *) (p :: * -> * -> *) (f :: * -> *) where
  expand   :: f (p a b) -> q ( a) ( b)
  contract :: q (f a) (f b) -> f (p a b)


-- | An example data type for `Biexpandcontract`
--
-- @
--  X a b = X (a, Maybe (Y a b))
--  Y a b = Y (b, Maybe (X a b))
--
--  Z a b = Either (X a b) (Y a b)
--
--  W a b = W (a, Maybe (W b a))
--  Z a b = Either (W a b) (W b a)
--  Z a b = let w x y = (x, Maybe (w y x)) in Either (w a b) (w b a)
-- @
--
--
-- @
--  [(a, b)]     -> ([a], [b])
--  [Either a b] -> Either (w a b) (flip w a b)
--  f (p a b)    -> p (g a b) (h a b)
-- @
--
-- @
--  Maybe (Either (NonEmpty a) (NonEmpty b), SwapList a b)
-- @
--
data SwapList a b = SwapLeft  a [a] (SwapList a b)
                  | SwapRight b [b] (SwapList a b)
                  | SwapEmpty
                  deriving (Eq, Ord, Show)

instance Bifunctor SwapList where
  bimap f g (SwapLeft  x xs s) = SwapLeft  (f x) (fmap f xs) (bimap f g s)
  bimap f g (SwapRight x xs s) = SwapRight (g x) (fmap g xs) (bimap f g s)
  bimap _ _  _                 = SwapEmpty

instance Swap SwapList where
  swap :: SwapList a b -> SwapList b a
  swap (SwapLeft  x xs s) = SwapRight x xs (swap s)
  swap (SwapRight x xs s) = SwapLeft  x xs (swap s)
  swap  _                 = SwapEmpty


-- | Uses `seqComonad`
instance Comonad f => Twist f SwapList where
  twist :: f (SwapList a b) -> Rope SwapList (f a) (f b)
  twist xs = Rope $ case extract xs of
                      SwapLeft  _ _ _ -> SwapLeft ((\(~(SwapLeft y _ _)) -> y) <$> xs)
                                                  (seqComonad . fmap (\(~(SwapLeft _ ys _)) -> ys) $ xs)
                                                  (pullRope . twist . fmap (\(~(SwapLeft _ _ s)) -> s) $ xs)
                      SwapRight _ _ _ -> pullRope . twist . fmap (\(~(SwapRight _ _ s)) -> s) $ xs
                      _               -> SwapEmpty

-- | Lazily seqence a `Comonad`, by recursively `tail`ing inside the `Functor`,
-- then using `catMaybes` and `maybeComonad` to extract the values.
seqComonad :: Comonad f => f [a] -> [f a]
seqComonad = catMaybes . fmap (maybeComonad . fmap listToMaybe) . iterate (fmap tail)

-- | `extract` to check whether it's `Nothing`, else use @`Just` . `fmap` `fromJust`@
maybeComonad :: Comonad f => f (Maybe a) -> Maybe (f a)
maybeComonad xs = maybe Nothing (\_ -> Just (fromJust <$> xs)) (extract xs)


-- | uses `leftExpand` and `rightExpand`
--
-- Notes:
--
-- @
-- contract :: q [a] [b] -> [Either a b]
--
-- [[a], [b], [a], [b], [a], [b]]
-- @
instance Biexpandcontract SwapList Either [] where
  expand   :: [Either a b] -> SwapList a b
  expand x = case x of
               (Left  x_:xs) -> leftExpand  (x_, []) xs
               (Right x_:xs) -> rightExpand (x_, []) xs
               (      _    ) -> SwapEmpty

  contract :: SwapList [a] [b] -> [Either a b]
  contract (SwapLeft  x xs xxs) = fmap Left  (P.concat (x:xs)) ++ contract xxs
  contract (SwapRight x xs xxs) = fmap Right (P.concat (x:xs)) ++ contract xxs
  contract (SwapEmpty         ) = []

-- | Expand a `SwapList` on the left
leftExpand :: (a, [a]) -> [Either a b] -> SwapList a b
leftExpand  (y, ys) (Left  z:zs) = leftExpand (y, ys++[z]) zs
leftExpand  (y, ys) (Right z:zs) = SwapLeft  y ys (rightExpand (z, []) zs)
leftExpand  (y, ys) (      _   ) = SwapLeft  y ys SwapEmpty

-- | Expand a `SwapList` on the right
rightExpand :: (b, [b]) -> [Either a b] -> SwapList a b
rightExpand (y, ys) (Left  z:zs) = SwapRight y ys (leftExpand (z, []) zs)
rightExpand (y, ys) (Right z:zs) = rightExpand (y, ys++[z]) zs
rightExpand (y, ys) (      _   ) = SwapRight y ys SwapEmpty




-- -- one way of thinking about this is distributing a partition on the image of a functor (C -> D) over the functor to get a new functor from C to the partitions?
-- --  Functor f => (f a -> partition (f a)) -> f (partition a) -> partition (f a)
-- -- OR we have a language formed along some scaffolding structure, for example a list, binary tree, etc. We also have a partition of the language on its own. We then want to map an arbitrary expression to a new, unique scaffolding structure where adjacent language terms within the scaffolding never are within the same equivalence classes within the language.
-- --  For example, if our partition is (isLeft) and our scaffolding structure is a list then the new scaffolding is formed like so:
-- --    [Either a b] -> Maybe (Either (Others a b) (Others b a))
-- --      Others x y = (x, Maybe (Others y x))
-- --
-- -- These are effectively factorizations of languages, as we move from a language built on scaffolding to a language of homogenous sublanguages built on two layers of scaffolding:
-- --    the original layer, that holds up the individual sublanguage of its slice of the partition
-- --    a layer, at least as constrained (likely smaller), that holds up the original layer
-- --  that is, this is a factorization of the scaffolding layers along a partition of the base language
-- --    if the splitting has nice properties, we may be able to show that there isn't any overlap between the two layers and so we can lift solutions on each to the total using some sort of disjoint (xor) sum.
-- --    this would allow type-solving to be split up between the languages, allowing study of each language to be immediately lifted to the study of both.
-- --      which is exactly what we want: nice liftings between the languages and localized addition/removal of features
-- --
-- --      one may define a structural fold, for example:
-- --        fold (x : ys) = fold_: x ys
-- --        fold []       = fold_[]
-- --
-- --        data Expr a where
-- --          App :: Expr a -> Expr a -> Expr a
-- --          Lit :: a
-- --
-- --        fold (App x y) = fold_App x y
-- --        fold (Lit x  ) = fold_Lit x
-- --      we then define a set of subterms to be adjacent iff there exists some GADT term of the form:
-- --        GADTerm :: subterm1 -> subterm2 -> subterm3 -> ... -> Expr
-- --      thus, we have that valid partitions are
-- --        let G be the graph formed by mapping adjacent sets to complete subgraphs
-- --        the partition forms a valid coloring of the resulting graph
-- --      Is a partition on an expression valid iff it is a valid coloring of that graph? YES
-- --    We thus have: iif the partition forms a valid coloring of every graph formed from an expression by connecting every vertex in a set of adjacent terms (GADT-wise) to every other in the set
-- --      The partition can be uniquely distributed into the terms of the language over some scaffolding structure (the language formed by joining adjacent and equal-kinded terms recursively)
-- --
-- --      We might want to define a "regular" or "homogenous" partition, one that partitions according to leaf-GADT terms?
-- --        e.g. isLeft partitions over the GADT terms, Left _ -> set1, Right _ -> set2
-- --        these seem more trivial, then it seems that we can do it iff no GADT-term is adjacent to itself? Mmmm, or adjacent to itself in an ambiguous way?
-- --        Hmmm.. it seems that we can make it work if we have an unambiguous and correct way to squash/fold adjacent terms..
-- --
-- --
-- --
-- -- What do we have?
-- --  We have some functor f from C -> D.
-- --  We have a binary relation on members of D (f a) that forms an undirected graph called isAdjacent.(?)
-- --  We have a partition on members of C (a)
-- -- With these together, we have that there is a unique way of mapping adjacent members of D with the same partition of C to a single member of `f (f a)`? Such that we get a new structure where
-- --  the structure of the adjacent members is pushed out into the leaves.
-- --
-- -- Functor f
-- -- fmap :: (a -> b) -> f a -> f b
-- -- (a -> Partition)
-- -- fmap (a -> Partition) -> f a -> f Partition
-- -- f a -> g (f a), where
-- --  part :: a -> Partition
-- --  unique :: Eq a => f a -> Maybe a :: if all the elements are equal, return just that element else nothing
-- --  fmap part :: f a -> f Partition
-- --  unique . fmap part :: f a -> Maybe a
-- --  mapM (unique . fmap part) :: g (f a) -> Maybe (g a)
-- --  isJust (mapM (unique . fmap part)) :: g (f a) -> Bool
-- --
-- -- Hmmm.. we seem to have two parts:
-- --  How do we specify the adjacency on the structure?
-- --  How do we specify the partition on the values?
-- --  How do we specify that we can join connected collections of adjacent values with the same partition? (join into the structure)
-- --
-- --  structure values
-- --  part :: values -> Partition
-- --  adjacent :: value in structure -> value in structure -> Bool
-- --  Mmmmm, we don't really care what the adjacency relation is, we only care that we have a partition on the structure such that we can group values together along that partition
-- --  What do we mean by group together? Well, we'd like a unique and consistent bijection betwwen: f a <-> f (f a) such that all of the a's in any substructure (f a) belong to the same partition.
-- --    A partition is just an injective function. So we want (f a -> whichPartition) for the inner layer.
-- --    (f a -> whichPartition) is the function :: (p :: a -> b) -> (f a | singleton . toSet . fmap p) -> b
-- --    Mmmm or really do we want: f a -> f (g a) -> (g a -> f a) -> f (f a)
-- -- 0
-- --  Ok, we have some structure and some structure preserving bijection that pushes as much of the structure inside the object structure?
-- --  f (g a) <-> f (g (f a))
-- --    T a => [T a] -> T [a]
-- --    T a b => [T a b] -> T [a] [b]
-- --    T a | U b => [T a b] -> [T [a] | U [b]]
-- --    (a -> b) => [a -> b] -> [a -> [b] | [a] -> b]
-- --    (a , b)  => Tree (a, b) -> Tree (Tree a, Tree b)
-- --    (a | b)  => Tree (a | b) -> Tree (Tree a | Tree b)
-- --    (a -> b) => Tree (a -> b) -> Tree (a -> Tree b | Tree a -> b)
-- --    a? => Tree a? -> Tree (Tree a)?
-- --      a? = a | _|_ = (?) a
-- --    [a] => Tree [a] -> Tree (Tree _|_ | Tree a | Tree (a, [x]) | Tree [x, a] | Tree [..])
-- --    ([a] = (:) a [a] :: [a] | [] :: [a]) => Tree [a] -> Tree [Tree a]
-- --
-- --    what are some valid partitions of some datatypes?
-- --      f (a) -> (f a)
-- --      f (a, b) -> (f a, f b) | (a, f b) | (f a, b)
-- --        f (a1, b1) (a2, b2) && a1 ~ b1 && a2 ~ b2 => (f a1 a2, f b1 b2)
-- --        f (a1, b1) (a2, b2) && a1 ~ a2 => (a1, f b1 b2)
-- --        f (a1, b1) (a2, b2) && b1 ~ b2 => (f a1 a2, b2)
-- --
-- --        f (g a1) (g a2) | a1 ~ a2 => g (f a1 a2)
-- --
-- --          fp :: t -> t -> Maybe t
-- --          f (g a1 b1) (g a2 b2) | fp a1 a2 && fp b1 b2 => g (fp a1 a2 ::   a) (fp b1 b2 ::   b)
-- --          f (g a1 b1) (g a2 b2) | fp a1 a2             => g (fp a1 a2 ::   a) (f  b1 b2 :: f b)
-- --          f (g a1 b1) (g a2 b2) |             fp b1 b2 => g (f  a1 a2 :: f a) (fp b1 b2 ::   b)
-- --          f (g a1 b1) (g a2 b2) |                      => f (f  a1 a2 :: f a) (f  b1 b2 :: f b)
-- --            What are we doing here? zipping the following function: If fp a1 a2 (we can join a1 and a2) then fp a1 a2 else f b1 b2
-- --              We must be able to do the following: (a1 -> a2 -> a3) -> (b1 -> b2 -> b3) -> g a1 b1 -> g a2 b2 -> g a3 b3
-- --              We must also be able to tell which of the zippings apply
-- --                (a1 -> a2 -> Either a3 (fa a1 a2)) -> (b1 -> b2 -> Either b3 (fb b1 b2)) -> g a1 b1 -> g a2 b2 -> g a3 b3 | g a3 (fb b1 b2) | g (fa a1 a2) b3 | g (fa a1 a2) (fb b1 b2)
-- --                c :: fa a -> fb b -> .. -> fz z -> c a b .. z
-- --                c :: fa a1 -> fa a2 -> c a1 a2
-- --                Left  :: a -> Either a b
-- --                Right :: b -> Either a b
-- --                fa :: a -> a -> f a
-- --                fb :: b -> b -> f b
-- --                f :: forall t. t -> t -> f t
-- --                _ :: (a -> a -> Either a (f a)) -> (b -> b -> Either b (f b)) -> Either a b -> Either a b -> Either a b | Either a (f b) | Either (f a) b | f (Either a b)
-- --                _ g h (F (Left  x) (Left  y)) = Left  (g x y)
-- --                _ g h (F (Right x) (Right y)) = Right (h x y)
-- --                _ g h (F        x         y ) = F x y
-- --                (a1 -> a2 -> Either a3 (c fa a1 -> fa a2 ->
-- --
-- --          [(1, 2), (1, 2)] => ([1, 1], [2, 2])
-- --          [(1, 2), (1, 3)] => (1, [2, 3])
-- --          [(1, 3), (2, 3)] => ([1, 2], 3)
-- --          [(1, 2), (3, 4)] => ([1, 3], [2, 4])
-- --
-- --      f (a | b) -> f a | f b
-- --      f (a | (a, b)) -> f a | (f a, f b) | (a, f b) | (f a, b)
-- --      f (a, b, c | d) -> (a, b, f c) |
-- --
-- --  f (g a) <-> f (f (g a)), f (f (g a)) <-> f (g (f a))
-- --  f . g <-> f . f . g <-> f . g . f
-- --    duplicate    :: Comonad f => f (g a) -> f (f (g a))
-- --
-- --    extract      :: Comonad f => f (f (g a)) -> f (g a)
-- --    fmap extract :: Comonad f => f (f (g a)) -> f (g a)
-- --
--   -- If f is a comonad then we have:
--   --  iso duplicate extract :: f (g a) <-> f (f (g a))
--   -- Suppose f is not a comonad, then do we have duplicate and extract?
--   --  qa      :: f (g a)     -> f (f (g a))
--   --  qb      :: f (f (g a)) -> f (g a)
--   --  qc      :: f (f (g a)) -> f (g (f a))
--   --  qd      :: f (g (f a)) -> f (f (g a))
--   --  qc . qa :: f (g a)     -> f (g (f a))
--   --  qb . qd :: f (g (f a)) -> f (g a)
--   --  qa . qb = id
--   --  qb . qa = id
--   --  qc . qd = id
--   --  qd . qc = id
--   --
--   --  f . g     = f . f . g
--   --  f . f . g = f . g . f
--   --  f . g     = f . g . f
--   --
--   --  (f . g) . f = (f . g . f) . f
--   --  qa      :: f . g     = f . f . g
--   --  qc      :: f . f . g -> f . g . f
--   --  qd      :: f (g (f a)) -> f (f (g a))
--   --  qc . qa :: f (g a)     -> f (g (f a))
--   --  qb . qd :: f (g (f a)) -> f (g a)
--   --
--   --
--   -- Note 1: we don't have any way to derive a function of the type: (f a -> a)
--   --  so we know that we can't get (Comonad f) for free
--   --
--   -- Note 2: we don't have any way to derive a function of the type: (g a -> a)
--   --  so we know that we can't get (Comonad g) for free
--   --
--   -- Note 3: we don't have any way to derive a function of the type: (a -> _)
--   --  so we know that we can't get Monad f, Monad g, Monad (f . g), Monad (g . f), etc for free
--   --
--   --  (f (g a) -> f (f (g a))) -> (f a -> f (f a))
--   --    wa :: f a -> f (g a)
--   --    wb :: f (f (g a)) -> f (f a)
--   --  (f (f (g a)) -> f (g a)) -> (f a -> a)
--   --    wc :: f a -> f (f (g a))
--   --    wd :: f (g a) -> a
--   --
--   --  wd . wa :: f a -> a
--   --  wb . wc :: f a -> f (f a)
--   --  With both:
--   --    (f (g a) -> a) . (f a -> f (g a)) = f a -> a
--   --
--   --  qq :: f (g a)     -> f (f (g a))
--   --  ww :: f (f (g a)) -> f (g a)
--   --  qq . ww = id
--   --  ww . qq = id
--   --
--   --  ww = extract = fmap extract
--   --  qq = duplicate
--   --  if this is the case, then I believe that it implies (g a <-> a)
--   --
--   --  extract   :: f a -> a
--   --  duplicate :: f a -> f (f a)
--   --  duplicate .      extract = id
--   --  duplicate . fmap extract = id
-- --
-- --    fmap distribute :: Functor     f, Distributive g => f (f (g a)) -> f (g (f a))
-- --    fmap sequenceA  :: Traversable f, Applicative  g => f (f (g a)) -> f (g (f a))
-- --
-- --    fmap distribute :: Distributive f, Functor     g => f (g (f a)) -> f (f (g a))
-- --    fmap sequenceA  :: Applicative  f, Traversable g => f (g (f a)) -> f (f (g a))
-- --
--   -- Functor f, Functor g
--   --  Comonad f
--   --    Distributive f, Distributive g
--   --    Distributive f, Traversable  f, Applicative g
--   --    Applicative  f, Traversable  g, Distributive g
--   --    Applicative  f, Traversable  g, Traversable f, Applicative g
-- --

-- Here's the idea: We take a list of some datatype t and we replace it with a list of t (_), such that consecutive elements of the same form (e.g. Left x, Left y || Right x, Right y || (x, y), (z, w)) are joined together along equivalences and the list pops out within the parameter (e.g. [(a, b1), (a, b2)] -> (a, [b1,b2])).
--   What's required for this to be unique is for the structures to be partitioned by their "join points".
--     Left (_ :: a), Right (_ :: b) -> Left (_ :: [a]), Right (_ :: [b])
--     (_ :: a, _ :: b) -> (_ :: a, _ :: b)
--     Nothing, Just (_ :: a) -> Nothing, Just [a]

--   Ahh, for it to be unique, each pair must map to either zero (don't match) or one (do match) possible combinations.
--     Question: Is this true iff there is one possible parsing of every sentence in such a language? Aka it is unambiguous?
--     Note: In other words, we have a binary relation:
--       (~) :: (a :: k :: L) -> (b :: k  :: L) -> ('Just (a ~~ b) :: Maybe k :: L)
--       (~) :: (a :: k :: L) -> (b :: k' :: L) -> ('Nothing       :: Maybe k :: L)
--     It must be at least left/right (right, wlog) associative for fixed k.
--       So we have three layers:
--         A language: L
--         The kind level (where terms with quivalent kinds combine)
--         The term level or GADT term level (The AST of the language)
--       If we attempt to combine two terms, for the combination to be unique, we must have that their kinds are equal (that is, the kinds must form a partition on the types)
--         Within a fixed kind, the operation must be associative (or just right/left associative?)
--         Between two kinds, I believe it may also be associative (hmm, it really probably only needs to be right/left associative)


--   An even stronger version forces a sequence on the resulting datatype, for example, for a type-sum over a pair, we have the language:
--     L = { a(ba)*, b(ab)* }
--   Where the L is equivalent to the language of sequences formed by squashing over a listlike or linear data structure
--     Note that in a complete binary tree as the outer structure, we instead have that the a,b's form a two-coloring of the binary tree. However, L is still the language generated, or more precisely:
--       a | b | \(x :: a) -> a, (b, (x :: a)), (b, (x :: a)) | \(x :: b) -> b, (a, (x :: b)), (a, (x :: b))
--     Thus it seems that the inner structure is determined by the outer one (In this case, the inner structure is L and the outer structure is Either)

-- In Scratch.FLang, we found that the laws:
--  f (g a) <-> f (f (g a)) <-> f (g (f a))
-- (Where the (<->) are bijections, and f,g are Functors.)
-- generate a regular language of the form: (F+)G(F?)
--  representing what is reachable from f (g a), i.e. the non-free part of the language.
-- This immediately shows that none of the following classes are implied:
--  Monad, Comonad, Applicative, Traversable, Distributive
-- Now, to clean out the edges.
--

-- f :: t -> t
-- g :: t -> t
-- a :: t

-- Let C be a category. F associates (X is an object in C and G(X) is as well)
--   a  :: X      => F(a) :: F(X)
--   f  :: X -> Y => F(f) :: F(X) -> F(Y)
--   id_X :: X -> X => F(id_X) = id_F(X) :: F(X) -> F(X)
--   f :: X -> Y, g :: Y -> Z, g . f :: X -> Z => F (g . f) = F(g) . F(f) :: F(X) -> F(Z)

--                      G associates (X is an object in C and G(X) is as well)
--   a  :: X      => G(a) :: G(X)
--   f  :: X -> Y => G(f) :: G(X) -> G(Y)
--   id_X :: X -> X => G(id_X) = id_G(X) :: G(X) -> G(X)
--   f :: X -> Y, g :: Y -> Z, g . f :: X -> Z => G (g . f) = G(g) . G(f) :: G(X) -> G(Z)

-- A is an object in C.

-- We want: functor isomorphisms between these compositions of F and G:
--   F(G(A))    -- we have a composition of functors
--   F(F(G(A))) -- we partition the outer functor into pieces such that `unique partition (xs :: f (g a))` is true for our partition (if it exists, of course, that's where graph coloring comes in)
--   F(G(F(A))) -- we push the partition into the inner functor, resulting in the connected (f (g a)) pieces being joined along their partitions.
--              -- In other words, it pulls the partition up to F's level while pushing the structure of F down into G. The structure of F is available to G in slices (local by definition of the partition).
--              -- finally, all of these operations are invertible since we have unique partitions
--              -- additionally, the functors which this works for are local functors and computers _really_ like computational and data locality. like they simply adore it.
--              --   computational locality makes stream and massively parallel processing a breeze (case in point, the line-by-line parser I just wrote)

--   f :: X -> Y => F(G(f)) :: F(G(X)) -> F(G(Y))

-- That is, we want three natural transformations that are also isomorphisms between those compositions.
--   X :: C => eta_1(X) :: F(G(X)) -> F(F(G(X))) :: C -> C
--   X :: C => eta_2(X) :: F(F(G(X))) -> F(G(F(X))) :: C -> C
--   X :: C => eta_3(X) :: F(G(F(X))) -> F(G(X)) :: C -> C

--   f :: X -> Y :: C -> C => eta_1(Y) . F(G(f)) = F(F(G(f))) . eta_1(X) :: F(G(X)) -> F(F(G(Y))) :: C -> C
--   f :: X -> Y :: C -> C => eta_2(Y) . F(F(G(f))) = F(G(F(f))) . eta_2(X) :: F(F(G(X))) -> F(G(F(Y))) :: C -> C
--   f :: X -> Y :: C -> C => eta_3(Y) . F(G(F(f))) = F(G(f)) . eta_3(X) :: F(G(F(X))) -> F(G(Y)) :: C -> C

-- We require these natural transformations to be bijections.

-- The three base words (those functor compositions) are equivalent
-- Functor composition is associative
-- We have a compositional identity, the identity functor

-- We thus have a group with the binary operation (.), identity the category identity, every element is invertible because we have isomorphisms between the compositions.
--   It has the presentation: f g = f f g = f g f
--   Since it is a group, we can form the language of elements equivalent to those three words.
--     This diagram makes it clear:
--
-- the lines are equivalence and the . is composition
--
--             (f . g)
--               / \
--              /   \
--             /     \
--            /       \
--           /         \
--   f . (f . g) --- (f . g) . f

-- First of all, we have the word "fg".
--   Next, we have the word formed by performing the substitution "fg -> fgf", namely "fgf".
--   Next, we have the word formed by performing the substitution "fg -> ffg", namely "ffg".

--   The substitution rules in full are as follows (with the substring "fg" wrapped in parentheses for emphasis alone):
--     "(fg)  -> f(fg)"
--     "f(fg) -> (fg)"
--     "(fg)  -> (fg)f"
--     "(fg)f -> (fg)"
--     "f(fg) -> (fg)f"
--     "(fg)f -> f(fg)"
--     ----------------
--       It's a rote exercise to show that any rule of the form "f?(fg)f? -> f?(fg)f?" can be derived.

--   Since the substring "fg" can never be broken by the available base rules, we simply have the ability to induct on "f?(fg)f? -> f?(fg)f?" to form "f{n}(fg)f{m}" for any n,m.
--     We simply compose the base rule with itself (max n m) times. We then resolve the optionals (?'s) to the number of "f"'s desired on either side of the "(fg)" center.
--   We thus have that this language is exactly the regular language: "(f*)(fg)(f*)"


-- One example application is [], Maybe, where pushing ([Maybe a] -> [Maybe [a]]) partitions by isJust. This is stream-friendly

-- Another example is ListT IO, Threaded, where Threaded is a comonad that evaluates its contents on extract, which we can do purely since we're still inside of ListT IO and couldn't do otherwise.
--   Pushing in is some parallel execution strategy

--   In other words, we can use this to treat monads as comonads. We just do: (Monad m => Turn (Compose m f) m) and the inner `m` can be treated as a comonad inside the turn.
--     I.e. we have: Monad m => m (Comonad m => ())
--     This could be well-typed if GHC supported impredicative polymorphism, but it doesn't.
--     How does it work?
--       Well, inside of `m`, we have extract (m (m a) -> m a), which is just join
--       Also, inside of `m`, we still have return so then we get duplicate (m (m a) -> m (m (m a))), which is return = fmap return

--     Inside of a comonad, we get a monad. This is the free comonad (/monad)

--   Ahhh, don't fotget about orthogonal lists, e.g. a 2d array. this may be able to pass layers in and out

-- Really, we want two applications of push to be equivalent to pure push (we don't gain anything from pushing more)
--   (the benefit is that it's equivalent to the limit of the other pushes OR you can consider it as a guarantee that everything to be pushed is pushed in the first push)


-- this is: "pushes are effectively idempotent" (using some "generic" injection into `f` to show that additional pushes do no more than the generic injection)
--   push  :: forall (a :: c). f (g a) -> f (g (f a))
--   puref :: forall (a :: c). a -> f a

--   push      . push :: forall (a :: c). f (g a) -> f (g (f (f a)))
--   fmap (fmap puref) . push :: forall (a :: c). f (g a) -> f (g (f (f a)))
--   push . push == fmap (fmap puref) . push

-- this is: "pushes are effectively idempotent" (using some "generic" extraction from `f` (which arguably, we can guarantee in some way when we want all of the strcuture of f that can be pushed to be))
--   push     :: forall (a :: c). f (g a) -> f (g (f a))
--   extractf :: forall (a :: c). f a -> a

--   push . push                :: forall (a :: c). f (g a) -> f (g (f (f a)))
--   fmap (fmap extractf) . push . push :: f (g a) -> f (g (f a))

--   fmap (fmap extractf) . push . push == push

-- this is: "pushes are effectively idempotent" (using some "generic" joining of `f`s)
--   push  :: forall (a :: c). f (g a) -> f (g (f a))
--   joinf :: forall (a :: c). f (f a) -> f a

--   push . push                :: forall (a :: c). f (g a) -> f (g (f (f a)))
--   fmap (fmap joinf) . push . push :: f (g a) -> f (g (f a))

--   fmap (fmap joinf) . push . push == push

-- this is: "pushes are effectively idempotent" (using some "generic" duplication of `f`'s)
--   push       :: forall (a :: c). f (g a) -> f (g (f a))
--   duplicatef :: forall (a :: c). f a -> f (f a)

--   push . push                :: forall (a :: c). f (g a) -> f (g (f (f a)))
--   fmap (fmap duplicatef) . push      :: forall (a :: c). f (g a) -> f (g (f (f a)))

--   fmap (fmap duplicatef) . push == push . push

-- I believe that the weakest version is a duplicate that is injective? Hmm, suppose we are within a context. This context is composable with itself.
--   We want any <-> 1, which is equivalent to having 2 <-> 1.
--   We want this to be a natural transformation.
--     Ahh, what if we had: f (f a) -> Maybe (f a)
--     Then, we could define the other mappings to match it so that it's always Just.
--   Regardless, we want to be able to show that the additional compositions provided by pushes are trivial.

-- Really, we probably want to have this property on the left as well, namely:
--     (in words: partitioning an already partitioned functor only adds a trivial layer, since the functor has already been partitioned)
--   partition :: f (g a)  -> f (f (g a))
--   fmap partition . partition = fmap puref . partition
--   fmap extract . fmap partition . partition = partition

-- To have everything be pushed/pulled through the (f . g) `joint`, we require that pushing/pulling are idempotent in some way. The question is, how can we most abstractly represent that these actions are idempotent? we don't necessarily have an equality or other properties of these functors. Our answer is that the action of a second push or pull is a so-called "least action":
--   push  :: forall (a :: c). f (g a) -> f (g (f a))
--   push . push                :: forall (a :: c). f (g a) -> f (g (f (f a)))
--   push . push = l_push . push
--   l_push :: forall (a :: c). f (g (f a)) -> f (g (f (f a)))
--     l_push is a least action from f (g (f a)) -> f (g (f (f a)))

--   we want to have the least action done possible between those two compositions of functors.
--   specifically, we want the least _left_ action.
--   what makes an action least?
--     well, I think that (return :: forall (a :: c). a -> f a) is a least action since there's no room for it to add more than the minimum amount of f's structure
--       ahhhh, if that doesn't exist, then the least amount of f's structure you could add would be:
--         (duplicate :: forall (a :: c). f a -> f (f a))
--       after that, it would be:
--         (_         :: g (f a) -> g (f (f a)))
--       and finally, after that, it would be:
--         (_         :: f (g (f a)) -> f (g (f (f a))))
--       But we want it to be independent of g's action, so we restrict our options to (return) and (duplicate).
--         finally, since (return, fmap return :: f a -> f (f a)), we may be able to restrict ourselves to needing duplicate.
--           return . return == fmap return . return?
--           fmap return . return == (>>= return . return) . return == \x -> (return x >>= (return . return)) == \x -> (return . return) x == return . return
--           Yes, QED
--       let's take the action to be duplicate.
--       now, we want it to be:
--         duplicate . duplicate = fmap duplicate . duplicate :: f a -> f (f (f a))
--       that is, the duplicates commute.
--       actually, if the duplicates commute then we don't have an original, e.g. f a -> f (f a), the original context could be left, right, or both.

--       what happens here, is that if it goes left, then (duplicate . duplicate) sends it all the way to the left and (fmap f . duplicate) does as well
--                                  if it goes right, then (duplicate . duplicate) sinds it to the right and (so does fmap f . duplicate)

--       ok, back to basics:
--         push :: f (g a) -> f (g (f a))
--         push . push :: f (g a) -> f (g (f (f a)))
--       we want (push . push) to be (tt . push)
--       tt :: f (g (f a)) -> f (g (f (f a)))
--       we want this f             ^ to be as close to trivial as possible. (I believe that it may be an isomorphism?)
--       how can we tell how trivial it is?
--         well consider:
--           fmap :: (a -> b) -> f a -> f b
--           fmap :: (a -> f a) -> f a -> f (f a)
--           fmap :: (f a -> f (f a)) -> f (g (f a)) -> f (g (f (f a)))
--                        ^
--             this is the one

--             one2 :: f (g (f a)) -> f (g (f (f a)))
--             we want the left one in (f (f a)) to be trivial.
--             for example:
--               one2 . one2 == fmap return . one2

--           fmap :: (g (f a) -> g (f (f a))) -> f (g (f a)) -> f (g (f (f a)))
--           fmap :: (g a -> f (g a)) -> f (g a) -> f (f (g a))
--             f (g a) -> f (f (g a)) -> f (f (f (g a)))
--             partition :: f (g a) -> f (f (g a))
--                          ^          ^  \individual partitioned sets
--                           \          \set of partitions
--                            \original set
--             fmap partition . partition :: f (g a) -> f (f (f (g a)))
--                                                  ^  ^  \the new partitioned sets
--                                                   \  \the new set of partitions
--                                                    \the set of new sets of partitions

--             two3' :: f (f (g a)) -> f (f (f (g a)))
--               we want the middle `f` in (f (f (f (g a)))) to be trivial
--             two3' = fmap (two3 :: f (g a) -> f (f (g a)))
--               we want the right `f` in (f (f (g a))) to be trivial

--             one2 :: f (g (f a)) -> f (g (f (f a))) (left  in (f . f) is trivial)
--                                          ^ at this point, the only resources we have are from the outer (f (g _))
--                                            this means that we can reduce a solution to a function of the type:
--                                            forall a. f (g a) -> f (g (f a))
--                                            (pushover :: f (f (g a)) -> f (g (f a))) . (two3 :: f a -> f (f a)))
--                                            (since this `f` cannot depend on (f a) for it to be trivial)
--             two3 :: f (g a)     -> f (f (g a))     (right in (f . f) is trivial)
--                                       ^ at this point, the only resources we have are from the outer (f _)
--                                       this means that we may be able to reduce a solution to a function of the type:
--                                       forall a. f a -> f (f a)
--                                                      ^ trivial
--                                       two3 . two3 == fmap two3 . two3
--                                       Hmm, if we say that the left side being trivial means that it cannot depend on f, and so it must be equal to (fmap _), then we get that:
--                                         (fmap return :: f a -> f (f a))
--                                       with the new requirement:
--                                         fmap return . return == return . return

--                                       (since this `f` cannot depend on (f a) for it to be trivial)
--               (when linearized (under vertical composition), these are commutative)
--               I believe that since (pushover :: f (f (g a)) -> f (g (f a))) is a natural transformation, we may be able to show that it preserves the triviality?

--             return :: a -> f a
--             fmap return :: f (g a) -> f (f (g a))
--             fmap (fmap return) . partition == fmap partition . partition :: f (g a) -> f (f (f (g a)))

--             fmap (fmap return) :: f (g a) -> f (g (f a))
--             fmap (fmap return) . push == push . push :: f (g a) -> f (g (f (f a)))

--             Joined f g
--               JoinedL f => (forall g. Functor g => Joined f g)
--               JoinedR g => (forall f. (Functor f, Pointed f) => Joined f g)
--             Functor f, Functor g
--             Natural transformations:
--               partition :: f (g a)     -> f (f (g a))
--               pushover  :: f (f (g a)) -> f (g (f a))
--               return    :: a -> f a

--             partition . pushover == push :: f (g a) -> f (g (f a))
--             fmap (fmap return) . partition == fmap partition . partition
--             fmap (fmap return) . push == push . push
--             fmap return == return . return

--             Joined2 f g where -- to convert between the two, use the curry/uncurry functors/natural transformations
--               partition2 :: f (g (a, b)) -> f (f (g (a, b)))
--               pushover2  :: f (f (g (a, b))) -> f (g (f a) (f b))
--               return     :: a -> f a

--             instance Joined2 [] Either where
--               partition2 :: [Either a b] -> [[Either a b]]
--               partition2 = groupBy ((==) `on` isLeft)

--               pushover2  :: [[Either a b]] -> [Either [a] [b]]
--               pushover2 = fmap (skipNull (\(x:xs) -> if isLeft x then Left (fromLeft <$> (x:xs)) else Right (fromRight <$> (x:xs))))

--               return     :: a -> [a]
--               return x = [x]

--             there is a canonical instance for foldable/unfoldable && g + coloring
--               you color the elements of (g a) with some valid coloring when considering some sort of adjacency on (f (g a))
--                 this forms the partition
--               you use the adjacency to cleanly form the pushover (the adjacency is on the endpoints of where f includes (g a) in (f (g a))

--                 that is, the coloring allows us to take the structure of f and since we have a connected component, we can extract this connected component
--                 we can then push this connected component cleanly inside of g
--                   f (g a) -> f (g_path a -> f a, g a)
--                   fmap (uncurry fmap) :: f (a -> f a, g a) -> f (g (f a))
--                in other words, each connected component of (f (g a)) forms a skeleton
--                  f (f a) -> f ({a} -> f a, {a})
--                  f (f a) -> f ((a -> Set) -> f a)
--                   f (g a) -> f ((a -> Set) -> g a)
--                   \(x :: f (g a)) -> ((f (g a) -> f ((a -> Set) -> g a)) x) <*> (fmap (fmap yoneda) x :: f (g (a -> Set)))

--                  ((h_a :: a -> Set) -> f a) <-> f a
--                  ((h_(f a) :: f a -> Set) -> f (f a)) <-> f (f a)

--                ergo, this works iff `f` has ((<*>) :: f (a -> b) -> f a -> f b) and the background category is locally small

--             another way to look at this is we have some polyfold: polyFoldr :: (forall u. Foldable u => u a -> b -> b) -> b -> t a -> b
--               g has zipWith
--               f is pointed, we have a semigroup over (f a)
--               f has polyfold
--               the polyfold on f gives a view into the internal sctructure, aka a partition
--               fmap (fmap (fmap return)) :: f (f (g a)) -> f (f (g (f a)))
--                 point the elements of `g`
--               ~polyfold (polyzip (<>))~ :: f (f (g (f a))) -> f (g (f a))
--                 fold the inner layer of `f` zipping (g (f a))'s along the lines of the builders for these (f (g (f a)))'s


--               unfoldr :: Functor g => (forall u. Foldable u => a -> u a) -> g a -> g (t a
--               if `f` is PolyFoldable and `g` is pointable: g a -> ((t :: A) -> g (t :: A), a :: A)
--               then we can

--             (partition) maps the original set to a set of partitions (the outer set, the universe set) and the partitions (the inner set)
--             (fmap partition . partition) maps the original set to the set of sets of partitions (the left set, the universe set) the singleton sets of the only partition in the subset (the middle set, singletons of partitions) the partitions (the right set)
--           So, what we want is to prove that the middle (f) is trivial (and possibly that (foldr ..) (_ :: f (g a)) is equal to (foldr (foldr ..)..) (_ :: f (f (g a))))
--           Question: can this depend on (g a)? Well yes, the partition can depend on the values of type (g a), e.g. isLeft


--             question, can we linearize this?
--               yeah, we just map words of functions of type :: f (g a) -> f (f (g a))
--               using the following patterns.
--                 f0
--                 fmap f0 . f1
--                 fmap (fmap f0) . fmap f1 . f2
--               equality preserves the lengths of words, because the words have unique types.
--               we want that (p=partition) "pp" -> "_p"
--               now what is this blank? hmm.

--         eta(x) :: f (g (f x)) -> f (g (f (f x)))
--         fn :: x -> y => eta(y) . f (g (f x)) == f (g (f (f x))) . eta(x)

--       eta^(-1)(x) . eta(y) . f (g (f x)) == f (g (f (f x)))
--       eta^(-1)(x) . eta(y) . f (g x) == f (f (g x))




--       we want the "real" one to stay fixed on the leftmost of the compositions of `f`s

--   going the other way, f (g a) -> f (f (g a))
--     for this one, we want:
--       partition :: forall (a :: c). f (g a) -> f (f (g a))
--       fmap partition . partition :: forall (a :: c). f (g a) -> f (f (f (g a)))
--     aka, the new rightmost layer should be a least action
--       fmap l_partition . partition :: forall (a :: c). f (g a) -> f (f (f (g a)))
--       l_partition :: forall (a :: c). f (f (g a)) -> f (f (f (g a)))
--     the least amount of structure you could add (on the right) would be:
--       (returnG :: forall a. g a -> f (g a))
--     after that:
--       (duplicateG :: forall a. f (g a) -> f (f (g a)))

--     fmap returnG :: forall a. f (g a) -> f (f (g a))

--     fmap returnG . returnG :: g a -> f (f (g a))

--     fmap (fmap returnG) . fmap returnG :: f (g a) -> f (f (f (g a)))

--     fmap^n returnG :: f^n (g a) -> f^(n+1) (g a)



--   or, do we want the free action for this? I'm not sure.
--     the least we can do to move from (f a -> f b) is the method that preserves the most we can using the definition of the functor: ((a -> b) -> (f a -> f b))
--     thus:
--       l_push = fmap (_ :: forall (a :: c). g (f a) -> g (f (f a)))
--       l_push =


-- Suppose we have some natural transformation: f . g -> f . h.
--   Is this equivalent to some natural transformation: g -> h, up to bijection?
--   One way, take f's identity natural transformation id_f :: f -> f.
--     then the left composition with (g -> h) is another natural transformation: (f . g -> f . h), and since id_f is a bijection this is as well.
--     QED
--   The other way, we have some natural transformation from (f . g -> f . h).
--     eta is a natural transformation from (f . g) to (f . h).
--     X :: C => eta_X :: (f . g) x -> (f . h) x
--     X :: C => beta_X :: g x -> h x
--     eta_Y . (f . g) fn = (f . h) fn . eta_X
--       fn :: X -> Y

--     eta_(beta_Y) . (f . g) fn = (f . h) fn . eta_(beta_X)

--     eta_X :: f x -> f x
--     beta_X :: g x -> h x

--   well this suggests that we can only go the other way when we have a bijection from (f . g) to (f . h)
--     otherwise, we wouldn't be able to form bijections between (eta_X :: (f . g) x -> (f . h) x) and (beta_X :: g x -> h x).
--       eta . f . beta . f' == (id :: (f . h) x -> (f . h) x) => f :: h x -> (f . g) x, f' :: (f . h) x -> g x
--       beta . g . eta . g' == (id :: h x -> h x) => g :: (f . h) x -> g x, g' :: h x -> (f . g) x

--     g == f . g
--     g == f . h
--     h == f . g
--     h == f . h
--     g == h

--     f == f . g

--   (g) must be a left identity of (f) under composition

--   -- Result:
--     an injective mapping from a natural transformation :: (g -> h) to one :: (f . g -> f . h) is trivial.
--     an injective mapping from a natural transformation :: (f . g -> f . h) to one :: (g -> h) exists iff (g == h) and (f == f . g), i.e. (g) must be a left identity of (f) under composition.






-- (monads, comonads, applicatives, all fall into this category, they all

-- question, is the limit of some functor inhabited? e.g.
--   The limit of Maybe is inhabited by:
--     Nothing
--     Just Nothing
--     Just (Just Nothing)
--     (the natural numbers)
--   The limit of (\x -> (a, x)) has exactly one inhabitant:
--     (a, (a, (a, (a, ..))))
--     (a right-infinite list)
--   The limit of (\x -> Either a x) has the inhabitants:
--     Left a
--     Right (Left a)
--     Right (Right (Left a)
--     (the pair (Nat, a))


-- what about expressing the limit of pushes? That's probably something like:
--   f (g a) -> f (g (Fix f a))
--   no... hmmm


-- class (Functor f, Functor g) => Join f g where
--   partition :: Iso'    (f (g a))  (f (f (g a)))
--   pushover  :: Iso' (f (f (g a))) (f (g (f a)))
--   push      :: Iso'    (f (g a))  (f (g (f a)))

-- newtype Threaded m a = Execute in a thread in m


-- f . g == f . g . f

-- f . g == (f . g) . f == ((f . g) . f) . f == (((f . g) . f) . f) . f
-- f . g == f . (f . g) == f . (f . (f . g)) == f . (f . (f . (f . g)))



-- a; a,b; a,b,a; a,b,a,b
-- b; b,a; b,a,b; b,a,b,a


-- -- f (p a b) <-> q (f a) (f b)



-- -- instance Functor f => Twist f Either where
-- --   twist xs = Rope _



-- -- | [Either a b] -> Rope Either [a] [b]
-- goal :: f (p a b) -> Rope p (f a) (f b)
-- goal = undefined


