module Types.Syntax
  ( BaseTy(..)
  , Ty(..)
  , baseTypes
  , baseIndex
  , baseTyStr
  ) where

import Test.QuickCheck
import Data.Map (Map)
import qualified Data.Map as Map

-- Contains ASTs for set-theoretic types that are convenient
-- when writing tests and/or programs but are not designed
-- for efficient computation (see LazyBDD.hs for that)


-- (Note: baseTypes and baseIndex depends on these defs;
--  modify them appropriately if BaseTy changes)
data BaseTy =
    T
  | F
  | Str
  | Null
  | Zero
  | One
  | ByteLargerThanOne
  | PosIndexNotByte
  | PosFixnumNotIndex
  | NegFixnum
  | PosIntegerNotFixnum
  | NegIntegerNotFixnum
  | PosRationalNotInteger
  | NegRationalNotInteger
  | FloatNaN
  | FloatPosZero
  | FloatNegZero
  | PosFloatNumber
  | PosFloatInfinity
  | NegFloatNumber
  | NegFloatInfinity
  | SingleFloatNaN
  | SingleFloatPosZero
  | SingleFloatNegZero
  | PosSingleFloatNumber
  | PosSingleFloatInfinity
  | NegSingleFloatNumber
  | NegSingleFloatInfinity
  | ExactImaginary
  | ExactComplex
  | FloatImaginary
  | SingleFloatImaginary
  | FloatComplex
  | SingleFloatComplex
  deriving (Eq, Show, Ord)
  

data Ty =
   Base BaseTy
  | Prod Ty Ty
  | Arrow Ty Ty
  | Or [Ty]
  | And [Ty]
  | Not Ty
  | Any
  | Empty
  | Name String -- Type name
  deriving (Eq, Show, Ord)


baseTypes :: [BaseTy]
baseTypes =
  [ T
  , F
  , Str
  , Null
  , Zero
  , One
  , ByteLargerThanOne
  , PosIndexNotByte
  , PosFixnumNotIndex
  , NegFixnum
  , PosIntegerNotFixnum
  , NegIntegerNotFixnum
  , PosRationalNotInteger
  , NegRationalNotInteger
  , FloatNaN
  , FloatPosZero
  , FloatNegZero
  , PosFloatNumber
  , PosFloatInfinity
  , NegFloatNumber
  , NegFloatInfinity
  , SingleFloatNaN
  , SingleFloatPosZero
  , SingleFloatNegZero
  , PosSingleFloatNumber
  , PosSingleFloatInfinity
  , NegSingleFloatNumber
  , NegSingleFloatInfinity
  , ExactImaginary
  , ExactComplex
  , FloatImaginary
  , SingleFloatImaginary
  , FloatComplex
  , SingleFloatComplex]

baseTyStr :: BaseTy -> String
baseTyStr T = "True"
baseTyStr F = "False"
baseTyStr Str = "String"
baseTyStr t = show t

baseIndexMap :: Map BaseTy Int
baseIndexMap = Map.fromList $ zip baseTypes [0..]

baseIndex :: BaseTy -> Int
baseIndex base = baseIndexMap Map.! base


-- * * * * * * * * * * * * * * * * * * * * * * *
-- QuickCheck related definitions
-- * * * * * * * * * * * * * * * * * * * * * * *


instance Arbitrary Ty where
  arbitrary = sized arbitrarySizedTy
  shrink = shrinkTy

arbitrarySizedTy :: Int -> Gen Ty
arbitrarySizedTy n
  | n < 2 = frequency [(30, pure (Base T))
                      ,(30, pure (Base F))
                      ,(30, pure (Base Zero))
                      ,(30, pure (Base One))
                      ,(5, pure Any)
                      ,(5, pure Empty)
                      ,(1, pure (Name "IntList"))
                      ,(1, pure (Name "NumList"))]
  | otherwise = do
      t1 <- (arbitrarySizedTy n')
      t2 <- (arbitrarySizedTy n')
      t3 <- (arbitrarySizedTy n')
      frequency [(5, pure (Base T))
                ,(5, pure (Base F))
                ,(10, pure (Base Zero))
                ,(10, pure (Base One))
                ,(15, pure (Prod t1 t2))
                ,(15, pure (Arrow t1 t2))
                ,(30, pure (Or [t1, t2]))
                ,(30, pure (Or [t1, t2, t3]))
                ,(10, pure (And [t1, t2]))
                ,(10, pure (And [t1, t2, t3]))
                ,(5, pure (Not t1))
                ,(1, pure Any)
                ,(1, pure Empty)]
    where n' = n `div` 2


shrinkTy :: Ty -> [Ty]
shrinkTy (Prod l r) = (shrink l)
                      ++ (shrink r)
                      ++ [Prod l' r' | (l', r') <- shrink (l, r)]
shrinkTy (Arrow d r) = (shrink d)
                      ++ (shrink r)
                      ++ [Arrow d' r' | (d', r') <- shrink (d, r)]
shrinkTy (Or [t1, t2]) = (shrink t1)
                       ++ (shrink t2)
                       ++ [t1,t2]
                       ++ [Or [t1', t2'] | (t1', t2') <- shrink (t1, t2)]
shrinkTy (Or [t1, t2, t3]) = (shrink t1)
                       ++ (shrink t2)
                       ++ (shrink t3)
                       ++ [t1,t2,t3]
                       ++ [Or [t1', t2'] | (t1', t2') <- shrink (t1, t2)]
                       ++ [Or [t2', t3'] | (t2', t3') <- shrink (t2, t3)]
                       ++ [Or [t1', t3'] | (t1', t3') <- shrink (t1, t3)]
shrinkTy (And [t1, t2]) = (shrink t1)
                        ++ (shrink t2)
                        ++ [t1,t2]
                        ++ [And [t1', t2'] | (t1', t2') <- shrink (t1, t2)]
shrinkTy (And [t1, t2, t3]) = (shrink t1)
                       ++ (shrink t2)
                       ++ (shrink t3)
                       ++ [t1,t2,t3]
                       ++ [And [t1', t2'] | (t1', t2') <- shrink (t1, t2)]
                       ++ [And [t2', t3'] | (t2', t3') <- shrink (t2, t3)]
                       ++ [And [t1', t3'] | (t1', t3') <- shrink (t1, t3)]
shrinkTy (Not t) = [Not t' | t' <- shrink t]
shrinkTy _ = []
