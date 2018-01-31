{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}

module Data.Fix where

import GHC.Generics (Generic)


-- | Simple fixed point newtype
newtype Fix f = Fix { runFix :: f (Fix f) } deriving (Generic)


-- | Convert a `Fix` to an infinite list
fixList :: Fix ((,) a) -> [a]
fixList (Fix ~(x, xs)) = x : fixList xs

-- | Warning: produces an infinite `String`
instance Show a => Show (Fix ((,) a)) where
  show = ("Fix " ++) . show . fixList


