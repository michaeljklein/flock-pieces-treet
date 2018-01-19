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
import Data.Biapplicative (Biapplicative(..), biliftA2)
import Data.Bifunctor (Bifunctor(..))
import Data.Either (isLeft, isRight)
import Data.Monoid ((<>))
import Prelude hiding (unlines, lines, id, (.))


-- | Distribute over a `Bifunctor`
class Bifunctor p => Bidistributable p f where
  -- | Later called "push" and or "push2"
  bidistribute :: f (p a b) -> f (p (f a) (f b))

-- | Equivalent to grouping the `Left` and `Right` values together, then sequencing:
--
-- @
--  Right . fmap (fromRight undefined) :: Functor f => f (Either a b) -> Either a (f b)
--  Left  . fmap (fromLeft  undefined) :: Functor f => f (Either a b) -> Either (f a) b
-- @
--
instance Bidistributable Either [] where
  bidistribute :: [Either a b] -> [Either [a] [b]]
  bidistribute (Left  x : xs) = uncurry (:)        . bimap              (Left  . (x :) . fmap (\(~(Left  y)) -> y)) bidistribute . Prelude.span isLeft  $ xs
  bidistribute (Right x : xs) = uncurry (flip (:)) . bimap bidistribute (Right . (x :) . fmap (\(~(Right y)) -> y)) .              Prelude.span isRight $ xs
  bidistribute  _             = []



class Swap p where
  swap :: p a b -> p b a

instance Swap (,) where
  swap ~(x, y) = (y, x)

instance Swap Either where
  swap  (Left  x) = Right x
  swap ~(Right x) = Left  x



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




-- | Commonly used variable types:
--
-- @
-- f :: t -> t
-- g :: t -> t
-- a :: t
-- @
--
commonVariableTypes :: ()
commonVariableTypes = ()


-- | Let @C@ be a category. @F@ associates (@X@ is an object in @C@ and @G(X)@ is as well):
--
-- @
--   a  :: X      => F(a) :: F(X)
--   f  :: X -> Y => F(f) :: F(X) -> F(Y)
--   id_X :: X -> X => F(id_X) = id_F(X) :: F(X) -> F(X)
--   f :: X -> Y, g :: Y -> Z, g . f :: X -> Z => F (g . f) = F(g) . F(f) :: F(X) -> F(Z)
--
--                      G associates (X is an object in C and G(X) is as well)
--   a  :: X      => G(a) :: G(X)
--   f  :: X -> Y => G(f) :: G(X) -> G(Y)
--   id_X :: X -> X => G(id_X) = id_G(X) :: G(X) -> G(X)
--   f :: X -> Y, g :: Y -> Z, g . f :: X -> Z => G (g . f) = G(g) . G(f) :: G(X) -> G(Z)
-- @
--
functorNotes :: ()
functorNotes = ()


-- | We want: functor isomorphisms between these compositions of F and G:
--
-- @
--   F(G(A))    -- we have a composition of functors
--   F(F(G(A))) -- we partition the outer functor into pieces such that `unique partition (xs :: f (g a))` is true for our partition (if it exists, of course, that's where graph coloring comes in)
--   F(G(F(A))) -- we push the partition into the inner functor, resulting in the connected (f (g a)) pieces being joined along their partitions.
-- @
--
-- In other words, it pulls the partition up to F's level while pushing the structure of F down into G. The structure of F is available to G in slices (local by definition of the partition).
--
-- Note: all of these operations are invertible since we have unique partitions.
--
-- Additionally, the functors which this works for are local functors and computers _really_ like computational and data locality. Like they simply adore it.
-- Computational locality makes stream and massively parallel processing a breeze (case in point, the line-by-line parser I just wrote)
--
functorIsomorphismCompositions :: ()
functorIsomorphismCompositions = ()


-- | That is, we want three natural transformations that are also isomorphisms between those compositions.
--
-- @
--   f :: X -> Y => F(G(f)) :: F(G(X)) -> F(G(Y))
--
--   X :: C => eta_1(X) :: F(G(X)) -> F(F(G(X))) :: C -> C
--   X :: C => eta_2(X) :: F(F(G(X))) -> F(G(F(X))) :: C -> C
--   X :: C => eta_3(X) :: F(G(F(X))) -> F(G(X)) :: C -> C
--
--   f :: X -> Y :: C -> C => eta_1(Y) . F(G(f)) = F(F(G(f))) . eta_1(X) :: F(G(X)) -> F(F(G(Y))) :: C -> C
--   f :: X -> Y :: C -> C => eta_2(Y) . F(F(G(f))) = F(G(F(f))) . eta_2(X) :: F(F(G(X))) -> F(G(F(Y))) :: C -> C
--   f :: X -> Y :: C -> C => eta_3(Y) . F(G(F(f))) = F(G(f)) . eta_3(X) :: F(G(F(X))) -> F(G(Y)) :: C -> C
-- @
--
-- We require these natural transformations to be bijections.
--
-- @
-- The three base words (those functor compositions) are equivalent
-- Functor composition is associative
-- We have a compositional identity, the identity functor
-- @
--
naturalIsomorphisms :: ()
naturalIsomorphisms = ()


-- | We thus have a group with the binary operation (.), identity the category identity, every element is invertible because we have isomorphisms between the compositions.
--
-- It has the presentation: @f g = f f g = f g f@.
--
-- Since it is a group, we can form the language of elements equivalent to those three words.
--
-- This diagram makes it clear:
--
-- (the lines are equivalence and the . is composition)
--
-- @
--
--             (f . g)
--               / \
--              /   \
--             /     \
--            /       \
--           /         \
--   f . (f . g) --- (f . g) . f
-- @

-- | First of all, we have the word "fg".
--
-- @
--   Next, we have the word formed by performing the substitution "fg -> fgf", namely "fgf".
--   Next, we have the word formed by performing the substitution "fg -> ffg", namely "ffg".
-- @
--
-- The substitution rules in full are as follows (with the substring "fg" wrapped in parentheses for emphasis alone):
--
-- @
--  "(fg)  -> f(fg)"
--  "f(fg) -> (fg)"
--  "(fg)  -> (fg)f"
--  "(fg)f -> (fg)"
--  "f(fg) -> (fg)f"
--  "(fg)f -> f(fg)"
--  ----------------
--    It's a rote exercise to show that any rule of the form "f?(fg)f? -> f?(fg)f?" can be derived.
-- @
--
-- Since the substring "fg" can never be broken by the available base rules, we simply have the ability to induct on "f?(fg)f? -> f?(fg)f?" to form "f{n}(fg)f{m}" for any n,m.
--
-- We simply compose the base rule with itself (max n m) times. We then resolve the optionals (?'s) to the number of "f"'s desired on either side of the "(fg)" center.
--
-- We thus have that this language is exactly the regular language: @"(f*)(fg)(f*)"@
--
regularLanguage :: ()
regularLanguage = ()


-- | One example application is @[], Maybe@, where pushing @([Maybe a] -> [Maybe [a]])@ partitions by isJust. This is stream-friendly.
--
-- Another example is @ListT IO, Threaded@, where @Threaded@ is a comonad that evaluates its contents on extract,
-- which we can do purely since we're still inside of @ListT IO@ and couldn't do otherwise.
--
-- Pushing in is some parallel execution strategy, in that case.
--
-- In other words, we can use this to treat monads as comonads. We just do: @(Monad m => Turn (Compose m f) m)@ and the inner @m@ can be treated as a comonad inside the turn.
--
-- I.e. we have: @Monad m => m (Comonad m => ())@
--
-- This could be well-typed if GHC supported impredicative polymorphism, but it doesn't.
--
-- How does it work?
--
-- @
--  Well, inside of `m`, we have extract (m (m a) -> m a), which is just join
--  Also, inside of `m`, we still have return so then we get duplicate (m (m a) -> m (m (m a))), which is return = fmap return
-- @
--
-- Inside of a comonad, we get a monad. This is the free comonad (/monad)
--
-- Ahhh, don't forget about orthogonal lists, e.g. a 2d array. this may be able to pass layers in and out
exampleApplications :: ()
exampleApplications = ()

-- | Really, we want two applications of push to be equivalent to pure push (we don't gain anything from pushing more)
--   (the benefit is that it's equivalent to the limit of the other pushes OR you can consider it as a guarantee that everything to be pushed is pushed in the first push)
--
-- This is: "pushes are effectively idempotent"
-- (using some "generic" injection into `f` to show that additional pushes do no more than the generic injection)
--
-- @
--   push  :: forall (a :: c). f (g a) -> f (g (f a))
--   puref :: forall (a :: c). a -> f a
--
--   push      . push :: forall (a :: c). f (g a) -> f (g (f (f a)))
--   fmap (fmap puref) . push :: forall (a :: c). f (g a) -> f (g (f (f a)))
--   push . push == fmap (fmap puref) . push
-- @
--
-- This is: "pushes are effectively idempotent"
-- (using some "generic" extraction from `f` (which arguably, we can guarantee in some way when we want all of the strcuture of f that can be pushed to be))
--
-- @
--   push     :: forall (a :: c). f (g a) -> f (g (f a))
--   extractf :: forall (a :: c). f a -> a
--
--   push . push                :: forall (a :: c). f (g a) -> f (g (f (f a)))
--   fmap (fmap extractf) . push . push :: f (g a) -> f (g (f a))
--
--   fmap (fmap extractf) . push . push == push
-- @
--
-- This is: "pushes are effectively idempotent"
-- (using some "generic" joining of `f`s)
--
-- @
--   push  :: forall (a :: c). f (g a) -> f (g (f a))
--   joinf :: forall (a :: c). f (f a) -> f a
--
--   push . push                :: forall (a :: c). f (g a) -> f (g (f (f a)))
--   fmap (fmap joinf) . push . push :: f (g a) -> f (g (f a))
--
--   fmap (fmap joinf) . push . push == push
-- @
--
-- This is: "pushes are effectively idempotent"
-- (using some "generic" duplication of `f`'s)
--
-- @
--   push       :: forall (a :: c). f (g a) -> f (g (f a))
--   duplicatef :: forall (a :: c). f a -> f (f a)
--
--   push . push                :: forall (a :: c). f (g a) -> f (g (f (f a)))
--   fmap (fmap duplicatef) . push      :: forall (a :: c). f (g a) -> f (g (f (f a)))
--
--   fmap (fmap duplicatef) . push == push . push
-- @
--
effectiveIdempotencePush :: ()
effectiveIdempotencePush = ()



-- | I believe that the weakest version is a duplicate that is injective?
--
-- Hmm, suppose we are within a context. This context is composable with itself.
--
-- - We want any <-> 1, which is equivalent to having 2 <-> 1.
-- - We want this to be a natural transformation.
--   * Ahh, what if we had: f (f a) -> Maybe (f a)
--   * Then, we could define the other mappings to match it so that it's always Just.
--
-- Regardless, we want to be able to show that the additional compositions provided by pushes are trivial.
weakestVersionDuplicate :: ()
weakestVersionDuplicate = ()


-- | Really, we probably want to have this property on the left as well, namely:
-- partitioning an already partitioned functor only adds a trivial layer, since the functor has already been partitioned.
--
-- @
--   partition :: f (g a)  -> f (f (g a))
--   fmap partition . partition = fmap puref . partition
--   fmap extract . fmap partition . partition = partition
-- @
--
leftPartitionProperty :: ()
leftPartitionProperty = ()


-- To have everything be pushed/pulled through the (f . g) `joint`, we require that pushing/pulling are idempotent in some way.
--
-- The question is, how can we most abstractly represent that these actions are idempotent?
--
-- We don't necessarily have an equality or other properties of these functors.
--
-- Our answer is that the action of a second push or pull is a so-called "least action":
--
-- @
--   push  :: forall (a :: c). f (g a) -> f (g (f a))
--   push . push                :: forall (a :: c). f (g a) -> f (g (f (f a)))
--   push . push = l_push . push
--   l_push :: forall (a :: c). f (g (f a)) -> f (g (f (f a)))
--     l_push is a least action from f (g (f a)) -> f (g (f (f a)))
-- @
--
leastActionExhaustivity :: ()
leastActionExhaustivity = ()


-- We want to have the least action done possible between those two compositions of functors.
--
-- Specifically, we want the least _left_ action.
--
--
-- What makes an action least?
--
-- Well, I think that @(return :: forall (a :: c). a -> f a)@ is a least action since there's no room for it to add more than the minimum amount of f's structure.
--
-- Ahhhh, if that doesn't exist, then the least amount of f's structure you could add would be:
--
-- @
--    (duplicate :: forall (a :: c). f a -> f (f a))
--  after that, it would be:
--    (_         :: g (f a) -> g (f (f a)))
--  and finally, after that, it would be:
--    (_         :: f (g (f a)) -> f (g (f (f a))))
--  But we want it to be independent of g's action, so we restrict our options to (return) and (duplicate).
--    finally, since (return, fmap return :: f a -> f (f a)), we may be able to restrict ourselves to needing duplicate.
--      return . return == fmap return . return?
--      fmap return . return == (>>= return . return) . return == \x -> (return x >>= (return . return)) == \x -> (return . return) x == return . return
--      Yes, QED
--  let's take the action to be duplicate.
--  now, we want it to be:
--    duplicate . duplicate = fmap duplicate . duplicate :: f a -> f (f (f a))
--  that is, the duplicates commute.
--  actually, if the duplicates commute then we don't have an original, e.g. f a -> f (f a), the original context could be left, right, or both.
--
--  what happens here, is that if it goes left, then (duplicate . duplicate) sends it all the way to the left and (fmap f . duplicate) does as well
--                             if it goes right, then (duplicate . duplicate) sinds it to the right and (so does fmap f . duplicate)
-- @
--
leastLeftAction :: ()
leastLeftAction = ()


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


-- | Question: can we linearize this?
--
-- Yes, we just map words of functions of type @f (g a) -> f (f (g a))@ using the following patterns:
--
-- @
--  f0
--  fmap f0 . f1
--  fmap (fmap f0) . fmap f1 . f2
-- @
--
-- Quality preserves the lengths of words, because the words have unique types.
--
-- We want that (@p=partition@):
--
-- @
-- "pp" -> "_p"
-- @
--
-- Now, what is this blank? Hmm.
--
-- @
--  eta(x) :: f (g (f x)) -> f (g (f (f x)))
--  fn :: x -> y => eta(y) . f (g (f x)) == f (g (f (f x))) . eta(x)
--
--  eta^(-1)(x) . eta(y) . f (g (f x)) == f (g (f (f x)))
--  eta^(-1)(x) . eta(y) . f (g x) == f (f (g x))
-- @
--
-- We want the "real" one to stay fixed on the leftmost of the compositions of `f`s.
linearizationQuestion :: ()
linearizationQuestion = ()


-- Going the other way, @f (g a) -> f (f (g a))@.
--
-- For this one, we want:
--
-- @
--  partition :: forall (a :: c). f (g a) -> f (f (g a))
--  fmap partition . partition :: forall (a :: c). f (g a) -> f (f (f (g a)))
-- @
--
-- In other words, the new rightmost layer should be a least action.
--
-- @
--  fmap l_partition . partition :: forall (a :: c). f (g a) -> f (f (f (g a)))
--  l_partition :: forall (a :: c). f (f (g a)) -> f (f (f (g a)))
-- @
--
-- The least amount of structure you could add (on the right) would be:
--
-- @
--  (returnG :: forall a. g a -> f (g a))
-- @
--
-- After that:
--
-- @
--  (duplicateG :: forall a. f (g a) -> f (f (g a)))
--
--  fmap returnG :: forall a. f (g a) -> f (f (g a))
--
--  fmap returnG . returnG :: g a -> f (f (g a))
--
--  fmap (fmap returnG) . fmap returnG :: f (g a) -> f (f (f (g a)))
--
--  fmap^n returnG :: f^n (g a) -> f^(n+1) (g a)
-- @
--
--
-- Or, do we want the free action for this? I'm not sure.
--
-- The least we can do to move from @(f a -> f b)@ is the method that preserves the most we can using the definition of the functor:
--
-- @
--  ((a -> b) -> (f a -> f b))
--
--  Thus:
--
--  l_push = fmap (_ :: forall (a :: c). g (f a) -> g (f (f a)))
-- @
--
goingTheOtherWayLeastActions :: ()
goingTheOtherWayLeastActions = ()


-- | Suppose we have some natural transformation: @f . g -> f . h@.
--   Is this equivalent to some natural transformation: @g -> h@, up to bijection?
--
--
-- One way, take @f@'s identity natural transformation @id_f :: f -> f@.
-- Then the left composition with @(g -> h)@ is another natural transformation: @(f . g -> f . h)@, and since @id_f@ is a bijection this is as well. Q.E.D.
--
-- Another way, we have some natural transformation from @(f . g -> f . h)@.
--
-- @
--     eta is a natural transformation from (f . g) to (f . h).
--     X :: C => eta_X :: (f . g) x -> (f . h) x
--     X :: C => beta_X :: g x -> h x
--     eta_Y . (f . g) fn = (f . h) fn . eta_X
--       fn :: X -> Y
--
--     eta_(beta_Y) . (f . g) fn = (f . h) fn . eta_(beta_X)
--
--     eta_X :: f x -> f x
--     beta_X :: g x -> h x
-- @
--
-- Well, this suggests that we can only go the other way when we have a bijection from @(f . g)@ to @(f . h)@
--
-- Otherwise, we wouldn't be able to form bijections between @(eta_X :: (f . g) x -> (f . h) x)@ and @(beta_X :: g x -> h x)@.
--
-- @
--  eta . f . beta . f' == (id :: (f . h) x -> (f . h) x) => f :: h x -> (f . g) x, f' :: (f . h) x -> g x
--  beta . g . eta . g' == (id :: h x -> h x) => g :: (f . h) x -> g x, g' :: h x -> (f . g) x
-- @
--
-- @
--  g == f . g
--  g == f . h
--  h == f . g
--  h == f . h
--  g == h
--
--  f == f . g
-- @
--
-- @
--  (g) must be a left identity of (f) under composition
-- @
--
--   Results:
--
-- @
--  An injective mapping from a natural transformation :: (g -> h) to one :: (f . g -> f . h) is trivial.
--  An injective mapping from a natural transformation :: (f . g -> f . h) to one :: (g -> h) exists iff (g == h) and (f == f . g), i.e. (g) must be a left identity of (f) under composition.
-- @
--
naturalTransformationUpToBijection :: ()
naturalTransformationUpToBijection = ()


-- | Question, is the limit of some functor inhabited? e.g.
--
-- @
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
-- @
--
-- what about expressing the limit of pushes? That's probably something like:
--
-- @
--   f (g a) -> f (g (Fix f a))
--   no... hmmm
-- @
--
functorLimitNotes :: ()
functorLimitNotes = ()


-- | Some notes on composing sequences of functors
--
-- @
-- f . g == f . g . f
-- f . g == (f . g) . f == ((f . g) . f) . f == (((f . g) . f) . f) . f
-- f . g == f . (f . g) == f . (f . (f . g)) == f . (f . (f . (f . g)))
-- @
--
-- @
-- a; a,b; a,b,a; a,b,a,b
-- b; b,a; b,a,b; b,a,b,a
-- @
--
functorCompositionNotes :: ()
functorCompositionNotes = ()

