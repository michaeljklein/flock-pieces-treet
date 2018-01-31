{-# LANGUAGE InstanceSigs #-}

module Data.Functor.Result where

import Control.Applicative (liftA2)


-- | `Object`, but with a sum (`Either`) instead of a tuple
data Result f b c = Result { getResult :: Either c (Effect f b c) }

-- | `Action`, but with a sum (`Either`) instead of a tuple
data Effect f b c = Effect { runEffect :: f      b (Result f b c) }


instance Functor (f b) => Functor (Result f b) where
  fmap f (Result x) = Result (either (Left . f) (Right . fmap f) x)

instance Functor (f b) => Functor (Effect f b) where
  fmap f (Effect x) = Effect (fmap f <$> x)


instance Applicative (f b) => Applicative (Result f b) where
  pure = Result . Left

  (<*>) :: Result f b (c -> d) -> Result f b c -> Result f b d
  Result (Left fs) <*> Result (Left xs) = Result (Left (fs xs))
  Result (Right fs) <*> Result (Right xs) = Result (Right (fs <*> xs))
  Result (Left fs) <*> Result (Right xs) = Result (Right (fmap fs xs))
  Result (Right fs) <*> Result (Left xs) = Result (Right (fmap ($ xs) fs))


instance Applicative (f b) => Applicative (Effect f b) where
  pure = Effect . pure . pure

  (<*>) :: Effect f b (c -> d) -> Effect f b c -> Effect f b d
  Effect fs <*> Effect xs = Effect (liftA2 (<*>) fs xs)


-- | Note that while both `Result` and `Effect` require `Applicative` for an `Applicative` instance,
-- `Result` only needs a `Functor` instance to implement `>>=`.
instance Applicative (f b) => Monad (Result f b) where
  return = pure

  (>>=) :: Result f b c -> (c -> Result f b d) -> Result f b d
  Result (Left  x) >>= f = f x
  Result (Right x) >>= f = Result (Right (Effect . fmap (>>= f) . runEffect $ x))


instance Monad (f b) => Monad (Effect f b) where
  return = pure

  (>>=) :: Effect f b c -> (c -> Effect f b d) -> Effect f b d
  Effect x >>= f = Effect (x >>= either (runEffect . f) (runEffect . (>>= f)) . getResult)



-- | Note: while this function has a simple type, if the `Result` cycles this functions result will be bottom
cycleSum :: Result Either a b -> Either a b
cycleSum (Result  (Left  x)) = Right x
cycleSum (Result ~(Right x)) = either Left cycleSum (runEffect x)


