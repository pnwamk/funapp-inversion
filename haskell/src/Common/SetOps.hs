module Common.SetOps
  ( subsets
  , strictSubsets
  , nonEmptySubsets
  ) where

import Data.List
import Data.Bits

-- powerset of a list
subsets :: (Eq a) => [a] -> [[a]]
subsets xs = combinations xs (\_ -> True)

-- powerset of a list minus original list
-- (i.e. all the strict subsets)
strictSubsets :: (Eq a) => [a] -> [[a]]
strictSubsets xs = combinations xs (\n -> not (allIncluded == n))
  where allIncluded = (2 ^ (length xs)) - 1
    
-- powerset of a list minus the empty list
-- (i.e. all the strict subsets)
nonEmptySubsets :: (Eq a) => [a] -> [[a]]
nonEmptySubsets xs = combinations xs (\n -> n > 0)


combinations :: (Eq a) => [a] -> (Int -> Bool) -> [[a]]
combinations xs include = aux 0
  where maxSize = (2 ^ (length xs))
        indexedData = zip xs [0..]
        aux cur = if (cur < maxSize)
                  then if (include cur)
                       then (gen cur):rest
                       else rest
                  else []
          where rest = aux (cur + 1)
                gen n = [x | (x , idx) <- indexedData, testBit n idx]
                     
