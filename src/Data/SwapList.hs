{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Data.SwapList where

import Control.Category (Category(..))
import Control.Comonad (Comonad(..))
import Data.Bifunctor (Bifunctor(..))
import Data.Maybe (fromJust, listToMaybe, catMaybes)
import Prelude hiding (unlines, lines, id, (.))
import Data.Bidistributable (Swap(..))
import Data.Rope (Rope(..), Twist(..))
import qualified Prelude as P (concat)



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




-- | One way of thinking about this is distributing a partition on the image of a functor @(C -> D)@ over the functor to get a new functor from C to the partitions.
--
-- @
--  Functor f => (f a -> partition (f a)) -> f (partition a) -> partition (f a)
-- @
--
-- OR we have a language formed along some scaffolding structure, for example a list, binary tree, etc.
-- We also have a partition of the language on its own.
-- We then want to map an arbitrary expression to a new, unique scaffolding structure,
-- where adjacent language terms within the scaffolding never are within the same equivalence classes within the language.
--
-- For example, if our partition is @(isLeft)@ and our scaffolding structure is a list then the new scaffolding is formed like so:
--
-- @
--  [Either a b] -> Maybe (Either (Others a b) (Others b a))
--  Others x y = (x, Maybe (Others y x))
-- @
--
introductionNotes :: ()
introductionNotes = ()


-- | Factorization of languages
--
-- These are effectively factorizations of languages, as we move from a language built on scaffolding to a language of homogenous sublanguages built on two layers of scaffolding:
--
--    the original layer, that holds up the individual sublanguage of its slice of the partition
--    a layer, at least as constrained (likely smaller), that holds up the original layer
--
-- That is, this is a factorization of the scaffolding layers along a partition of the base language.
--
-- If the splitting has nice properties, we may be able to show that there isn't any overlap between the two layers and so we can lift solutions on each to the total using some sort of disjoint (xor) sum.
--
-- This would allow type-solving to be split up between the languages, allowing study of each language to be immediately lifted to the study of both.
--
-- Which is exactly what we want: nice liftings between the languages and localized addition/removal of features.
--
--
-- One may define a structural fold, for example:
--
-- @
--  fold (x : ys) = fold_: x ys
--  fold []       = fold_[]
--
--  data Expr a where
--    App :: Expr a -> Expr a -> Expr a
--    Lit :: a
--
--  fold (App x y) = fold_App x y
--  fold (Lit x  ) = fold_Lit x
-- @
--
-- We then define a set of subterms to be adjacent iff there exists some GADT term of the form:
--
-- @
--  GADTerm :: subterm1 -> subterm2 -> subterm3 -> ... -> Expr
-- @
--
-- Thus, we have that valid partitions are
--
-- @
--  let G be the graph formed by mapping adjacent sets to complete subgraphs
--  the partition forms a valid coloring of the resulting graph
-- @
--
-- Question: Is a partition on an expression valid iff it is a valid coloring of that graph? YES.
--
--
-- We thus have: iif the partition forms a valid coloring of every graph formed from an expression by connecting every vertex in a set of adjacent terms (GADT-wise) to every other in the set.
--
-- The partition can be uniquely distributed into the terms of the language over some scaffolding structure (the language formed by joining adjacent and equal-kinded terms recursively)
--
-- We might want to define a "regular" or "homogenous" partition, one that partitions according to leaf-GADT terms?
--
-- @
--        e.g. isLeft partitions over the GADT terms, Left _ -> set1, Right _ -> set2
--        these seem more trivial, then it seems that we can do it iff no GADT-term is adjacent to itself? Mmmm, or adjacent to itself in an ambiguous way?
--        Hmmm.. it seems that we can make it work if we have an unambiguous and correct way to squash/fold adjacent terms..
-- @
--
factorizationOfLanguages :: ()
factorizationOfLanguages = ()



-- | What do we have?
--
-- @
--  We have some functor f from C -> D.
--  We have a binary relation on members of D (f a) that forms an undirected graph called isAdjacent.(?)
--  We have a partition on members of C (a)
-- @
--
-- With these together, we have that there is a unique way of mapping adjacent members of D with the same partition of C to a single member of `f (f a)`?
-- (Such that we get a new structure where the structure of the adjacent members is pushed out into the "leaves".)
--
-- @
--  Functor f
--  fmap :: (a -> b) -> f a -> f b
--  (a -> Partition)
--  fmap (a -> Partition) -> f a -> f Partition
--  f a -> g (f a), where
--   part :: a -> Partition
--   unique :: Eq a => f a -> Maybe a :: if all the elements are equal, return just that element else nothing
--   fmap part :: f a -> f Partition
--   unique . fmap part :: f a -> Maybe a
--   mapM (unique . fmap part) :: g (f a) -> Maybe (g a)
--   isJust (mapM (unique . fmap part)) :: g (f a) -> Bool
-- @
--
quickRecap :: ()
quickRecap = ()


-- | Hmmm.. we seem to have three parts:
--
-- @
--  How do we specify the adjacency on the structure?
--  How do we specify the partition on the values?
--  How do we specify that we can join connected collections of adjacent values with the same partition? (join into the structure)
-- @
--
-- @
--  structure values
--  part :: values -> Partition
--  adjacent :: value in structure -> value in structure -> Bool
-- @
--
-- Mmmmm, we don't really care what the adjacency relation is,
-- we only care that we have a partition on the structure such that we can group values together along that partition.
--
-- What do we mean by group together?
-- Well, we'd like a unique and consistent bijection betwwen: @f a <-> f (f a)@ such that all of the @a@'s in any substructure @(f a)@ belong to the same partition.
--
-- A partition is just an injective function.
-- So we want @(f a -> whichPartition)@ for the inner layer.
--
-- @(f a -> whichPartition)@ is the @function :: (p :: a -> b) -> (f a | singleton . toSet . fmap p) -> b@
--
-- Mmmm or really do we want:
--
-- @
--  f a -> f (g a) -> (g a -> f a) -> f (f a)
-- @
--
threePartsOfSpecification :: ()
threePartsOfSpecification = ()

-- | Ok, we have some structure and some structure preserving bijection that pushes as much of the structure inside the object structure?
--
-- @
--  f (g a) <-> f (g (f a))
--    T a => [T a] -> T [a]
--    T a b => [T a b] -> T [a] [b]
--    T a | U b => [T a b] -> [T [a] | U [b]]
--    (a -> b) => [a -> b] -> [a -> [b] | [a] -> b]
--    (a , b)  => Tree (a, b) -> Tree (Tree a, Tree b)
--    (a | b)  => Tree (a | b) -> Tree (Tree a | Tree b)
--    (a -> b) => Tree (a -> b) -> Tree (a -> Tree b | Tree a -> b)
--    a? => Tree a? -> Tree (Tree a)?
--      a? = a | _|_ = (?) a
--    [a] => Tree [a] -> Tree (Tree _|_ | Tree a | Tree (a, [x]) | Tree [x, a] | Tree [..])
--    ([a] = (:) a [a] :: [a] | [] :: [a]) => Tree [a] -> Tree [Tree a]
-- @
--
structurePreservingBijection :: ()
structurePreservingBijection = ()


-- | What are some valid partitions of some datatypes?
--
-- @
--  f (a) -> (f a)
--  f (a, b) -> (f a, f b) | (a, f b) | (f a, b)
--
--  f (a1, b1) (a2, b2) && a1 ~ b1 && a2 ~ b2 => (f a1 a2, f b1 b2)
--  f (a1, b1) (a2, b2) && a1 ~ a2 => (a1, f b1 b2)
--  f (a1, b1) (a2, b2) && b1 ~ b2 => (f a1 a2, b2)
--
--  f (g a1) (g a2) | a1 ~ a2 => g (f a1 a2)
-- @
--
-- @
--  fp :: t -> t -> Maybe t
--
--  f (g a1 b1) (g a2 b2) | fp a1 a2 && fp b1 b2 => g (fp a1 a2 ::   a) (fp b1 b2 ::   b)
--  f (g a1 b1) (g a2 b2) | fp a1 a2             => g (fp a1 a2 ::   a) (f  b1 b2 :: f b)
--  f (g a1 b1) (g a2 b2) |             fp b1 b2 => g (f  a1 a2 :: f a) (fp b1 b2 ::   b)
--  f (g a1 b1) (g a2 b2) |                      => f (f  a1 a2 :: f a) (f  b1 b2 :: f b)
-- @
--
-- What are we doing here? zipping the following function:
--
-- @
-- If fp a1 a2 (we can join a1 and a2) then fp a1 a2 else f b1 b2
-- @
--
-- We must be able to do the following:
--
-- @
--  (a1 -> a2 -> a3) -> (b1 -> b2 -> b3) -> g a1 b1 -> g a2 b2 -> g a3 b3
-- @
--
-- We must also be able to tell which of the zippings apply.
--
-- @
--        (a1 -> a2 -> Either a3 (fa a1 a2)) -> (b1 -> b2 -> Either b3 (fb b1 b2)) -> g a1 b1 -> g a2 b2 -> g a3 b3 | g a3 (fb b1 b2) | g (fa a1 a2) b3 | g (fa a1 a2) (fb b1 b2)
--        c :: fa a -> fb b -> .. -> fz z -> c a b .. z
--        c :: fa a1 -> fa a2 -> c a1 a2
--        Left  :: a -> Either a b
--        Right :: b -> Either a b
--        fa :: a -> a -> f a
--        fb :: b -> b -> f b
--        f :: forall t. t -> t -> f t
--        _ :: (a -> a -> Either a (f a)) -> (b -> b -> Either b (f b)) -> Either a b -> Either a b -> Either a b | Either a (f b) | Either (f a) b | f (Either a b)
--        _ g h (F (Left  x) (Left  y)) = Left  (g x y)
--        _ g h (F (Right x) (Right y)) = Right (h x y)
--        _ g h (F        x         y ) = F x y
--        (a1 -> a2 -> Either a3 (c fa a1 -> fa a2 ->
-- @
--
someValidPartitions :: ()
someValidPartitions = ()


-- | Misc. notes:
--
-- @
--  [(1, 2), (1, 2)] => ([1, 1], [2, 2])
--  [(1, 2), (1, 3)] => (1, [2, 3])
--  [(1, 3), (2, 3)] => ([1, 2], 3)
--  [(1, 2), (3, 4)] => ([1, 3], [2, 4])
-- @
--
-- @
--  f (a | b) -> f a | f b
--  f (a | (a, b)) -> f a | (f a, f b) | (a, f b) | (f a, b)
--  f (a, b, c | d) -> (a, b, f c) |
-- @
--
-- @
--  f (g a) <-> f (f (g a)), f (f (g a)) <-> f (g (f a))
--  f . g <-> f . f . g <-> f . g . f
--    duplicate    :: Comonad f => f (g a) -> f (f (g a))
--
--    extract      :: Comonad f => f (f (g a)) -> f (g a)
--    fmap extract :: Comonad f => f (f (g a)) -> f (g a)
--
-- @
--
someValidPartitionsNotes :: ()
someValidPartitionsNotes = ()


-- | If @f@ is a comonad then we have:
--
-- @
--  iso duplicate extract :: f (g a) <-> f (f (g a))
-- @
--
-- Suppose f is not a comonad, then do we have duplicate and extract?
--
-- @
--  qa      :: f (g a)     -> f (f (g a))
--  qb      :: f (f (g a)) -> f (g a)
--  qc      :: f (f (g a)) -> f (g (f a))
--  qd      :: f (g (f a)) -> f (f (g a))
--  qc . qa :: f (g a)     -> f (g (f a))
--  qb . qd :: f (g (f a)) -> f (g a)
--  qa . qb = id
--  qb . qa = id
--  qc . qd = id
--  qd . qc = id
--
--  f . g     = f . f . g
--  f . f . g = f . g . f
--  f . g     = f . g . f
--
--  (f . g) . f = (f . g . f) . f
--  qa      :: f . g     = f . f . g
--  qc      :: f . f . g -> f . g . f
--  qd      :: f (g (f a)) -> f (f (g a))
--  qc . qa :: f (g a)     -> f (g (f a))
--  qb . qd :: f (g (f a)) -> f (g a)
--
--
-- Note 1: we don't have any way to derive a function of the type: (f a -> a)
--  so we know that we can't get (Comonad f) for free
--
-- Note 2: we don't have any way to derive a function of the type: (g a -> a)
--  so we know that we can't get (Comonad g) for free
--
-- Note 3: we don't have any way to derive a function of the type: (a -> _)
--  so we know that we can't get Monad f, Monad g, Monad (f . g), Monad (g . f), etc for free
--
--  (f (g a) -> f (f (g a))) -> (f a -> f (f a))
--    wa :: f a -> f (g a)
--    wb :: f (f (g a)) -> f (f a)
--  (f (f (g a)) -> f (g a)) -> (f a -> a)
--    wc :: f a -> f (f (g a))
--    wd :: f (g a) -> a
--
--  wd . wa :: f a -> a
--  wb . wc :: f a -> f (f a)
--  With both:
--    (f (g a) -> a) . (f a -> f (g a)) = f a -> a
--
--  qq :: f (g a)     -> f (f (g a))
--  ww :: f (f (g a)) -> f (g a)
--  qq . ww = id
--  ww . qq = id
--
--  ww = extract = fmap extract
--  qq = duplicate
-- @
--
-- Ff this is the case, then I believe that it implies @(g a <-> a)@.
--
-- @
--  extract   :: f a -> a
--  duplicate :: f a -> f (f a)
--  duplicate .      extract = id
--  duplicate . fmap extract = id
--
--  fmap distribute :: Functor     f, Distributive g => f (f (g a)) -> f (g (f a))
--  fmap sequenceA  :: Traversable f, Applicative  g => f (f (g a)) -> f (g (f a))
--
--  fmap distribute :: Distributive f, Functor     g => f (g (f a)) -> f (f (g a))
--  fmap sequenceA  :: Applicative  f, Traversable g => f (g (f a)) -> f (f (g a))
--
--  Functor f, Functor g
--   Comonad f
--     Distributive f, Distributive g
--     Distributive f, Traversable  f, Applicative g
--     Applicative  f, Traversable  g, Distributive g
--     Applicative  f, Traversable  g, Traversable f, Applicative g
-- @
--
comonadComparison :: ()
comonadComparison = ()


-- | Series join points:
--
-- Here's the idea: We take a list (series) of some datatype @t@ and we replace it with a list of @t (_)@,
-- such that consecutive elements of the same form (e.g. @Left x, Left y || Right x, Right y || (x, y), (z, w)@)
-- are joined together along equivalences and the list pops out within the parameter (e.g. @[(a, b1), (a, b2)] -> (a, [b1,b2])@).
--
-- What's required for this to be a unique construction is for the structures to be partitioned by their "join points".
--
-- @
--  Left (_ :: a), Right (_ :: b) -> Left (_ :: [a]), Right (_ :: [b])
--  (_ :: a, _ :: b) -> (_ :: a, _ :: b)
--  Nothing, Just (_ :: a) -> Nothing, Just [a]
-- @
--
-- Ahh, for it to be unique, each pair must map to either zero (don't match) or one (do match) possible combinations.
--
-- Question: Is this true iff there is one possible parsing of every sentence in such a language?
-- In other words, it is unambiguous?
--
-- Note: In other words, we have a binary relation:
--
-- @
--  (~) :: (a :: k :: L) -> (b :: k  :: L) -> ('Just (a ~~ b) :: Maybe k :: L)
--  (~) :: (a :: k :: L) -> (b :: k' :: L) -> ('Nothing       :: Maybe k :: L)
-- @
--
-- It must be at least left/right (right, w.l.o.g.) associative for fixed @k@.
--
-- So we have three layers:
--
-- @
--  A language: L
--  The kind level (where terms with quivalent kinds combine)
--  The term level or GADT term level (The AST of the language)
-- @
--
-- If we attempt to combine two terms, for the combination to be unique, we must have that their kinds are equal (that is, the kinds must form a partition on the types).
--
-- @
--  Within a fixed kind, the operation must be associative (or just right/left associative?)
--  Between two kinds, I believe it may also be associative (hmm, it really probably only needs to be right/left associative)
-- @
--
seriesJoinPoints :: ()
seriesJoinPoints = ()


-- | An even stronger version forces a sequence on the resulting datatype, for example, for a type-sum over a pair, we have the language:
--
-- @
--  L = { a(ba)*, b(ab)* }
-- @
--
-- Where the language @L@ is equivalent to the language of sequences formed by squashing over a list-like or linear data structure.
--
-- Note: In a complete binary tree as the outer structure, we instead have that the @a,b@'s form a two-coloring of the binary tree.
-- However, @L@ is still the language generated.
--
-- More precisely:
--
-- @
--  a | b | \(x :: a) -> a, (b, (x :: a)), (b, (x :: a)) | \(x :: b) -> b, (a, (x :: b)), (a, (x :: b))
-- @
--
-- Thus it seems that the inner structure is determined by the outer one (In this case, the inner structure is L and the outer structure is Either)
strongerVersionSequence :: ()
strongerVersionSequence = ()


-- | In Data.FGLang, we found that the laws:
--
-- @
--  f (g a) <-> f (f (g a)) <-> f (g (f a))
-- @
--
-- (Where the @(<->)@ are bijections, and @f,g@ are Functors.)
-- generate a regular language of the form: @(F+)G(F?)@
--  representing what is reachable from @f (g a)@, i.e. the non-free part of the language.
--
-- This immediately shows that none of the following classes are implied:
--
-- @
--  Monad, Comonad, Applicative, Traversable, Distributive
-- @
--
dataFGLanglaws :: ()
dataFGLanglaws = ()


