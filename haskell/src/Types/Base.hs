module Types.Base
  ( Base(..)
  , emptyBase
  , anyBase
  , baseOr
  , baseAnd
  , baseDiff
  , baseNot
  ) where

import Data.Word
import Data.Bits

{-# INLINE (.\\.) #-}
(.\\.) :: Bits a => a -> a -> a
b1 .\\. b2 = b1 .&. (complement b2)

data Base = Base !Bool {-# UNPACK #-} !Word32
  deriving (Eq, Show, Ord)

emptyBase = Base True 0
anyBase   = Base False 0

{-# INLINE baseOr #-}
baseOr :: Base -> Base -> Base
baseOr (Base True pos1)  (Base True pos2)
  = Base True $ pos1 .|. pos2
baseOr (Base True pos)  (Base False neg)
  = Base False $ neg .\\. pos
baseOr (Base False neg) (Base True pos)
  = Base False $ neg .\\. pos
baseOr (Base False neg1) (Base False neg2)
  = Base False $ neg1 .&. neg2

{-# INLINE baseAnd #-}    
baseAnd :: Base -> Base -> Base
baseAnd (Base True pos1)  (Base True pos2)
  = Base True $ pos1 .&. pos2
baseAnd (Base True pos)  (Base False neg)
  = Base True $ pos .\\. neg
baseAnd (Base False neg) (Base True pos)
  = Base True $ pos .\\. neg
baseAnd (Base False neg1) (Base False neg2)
  = Base False $ neg1 .|. neg2

{-# INLINE baseDiff #-}
baseDiff :: Base -> Base -> Base
baseDiff (Base True pos1)  (Base True pos2)
  = Base True $ pos1 .\\. pos2
baseDiff (Base True pos)  (Base False neg)
  = Base True $ pos .&. neg
baseDiff (Base False neg) (Base True pos)
  = Base False $ pos .|. neg
baseDiff (Base False neg1) (Base False neg2)
  = Base True $ neg2 .\\. neg1

{-# INLINE baseNot #-}
baseNot :: Base -> Base
baseNot (Base sign bs) = Base (not sign) bs
