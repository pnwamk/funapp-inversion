module Types.Syntax where

import Test.QuickCheck
import Data.Map

-- Contains ASTs for set-theoretic types that are convenient
-- when writing tests and/or programs but are not designed
-- for efficient computation (see LazyBDD.hs for that)

data Ty =
  -- Base Types
  -- (Note: baseTypes below depends on these;
  --  modify baseTypes appropriately if these change)
    T
  | F
  | Str
  | Zero
  | One
  | ByteLargerThanOne
  | PositiveIndexNotByte
  | PositiveFixnumNotIndex
  | NegativeFixnum
  | PositiveIntegerNotFixnum
  | NegativeIntegerNotFixnum
  | PositiveRationalNotInteger
  | NegativeRationalNotInteger
  | FloatNaN
  | FloatPositiveZero
  | FloatNegativeZero
  | PositiveFloatNumber
  | PositiveFloatInfinity
  | NegativeFloatNumber
  | NegativeFloatInfinity
  | SingleFloatNaN
  | SingleFloatPositiveZero
  | SingleFloatNegativeZero
  | PositiveSingleFloatNumber
  | PositiveSingleFloatInfinity
  | NegativeSingleFloatNumber
  | NegativeSingleFloatInfinity
  | ExactImaginary
  | ExactComplex
  | FloatImaginary
  | SingleFloatImaginary
  | FloatComplex
  | SingleFloatComplex
  -- End of Base Types
  | Prod Ty Ty
  | Arrow Ty Ty
  | Or [Ty]
  | And [Ty]
  | Not Ty
  | Any
  | Empty
  deriving (Eq, Show, Ord)

baseTypes :: [Ty]
baseTypes =
  [ T
  , F
  , Str
  , Zero
  , One
  , ByteLargerThanOne
  , PositiveIndexNotByte
  , PositiveFixnumNotIndex
  , NegativeFixnum
  , PositiveIntegerNotFixnum
  , NegativeIntegerNotFixnum
  , PositiveRationalNotInteger
  , NegativeRationalNotInteger
  , FloatNaN
  , FloatPositiveZero
  , FloatNegativeZero
  , PositiveFloatNumber
  , PositiveFloatInfinity
  , NegativeFloatNumber
  , NegativeFloatInfinity
  , SingleFloatNaN
  , SingleFloatPositiveZero
  , SingleFloatNegativeZero
  , PositiveSingleFloatNumber
  , PositiveSingleFloatInfinity
  , NegativeSingleFloatNumber
  , NegativeSingleFloatInfinity
  , ExactImaginary
  , ExactComplex
  , FloatImaginary
  , SingleFloatImaginary
  , FloatComplex
  , SingleFloatComplex]

baseTyStr :: Ty -> String
baseTyStr T = "True"
baseTyStr F = "False"
baseTyStr Str = "String"
baseTyStr Zero = "Zero"
baseTyStr One = "One"
baseTyStr ByteLargerThanOne = "ByteLargerThanOne"
baseTyStr PositiveIndexNotByte = "PositiveIndexNotByte"
baseTyStr PositiveFixnumNotIndex = "PositiveFixnumNotIndex"
baseTyStr NegativeFixnum = "NegativeFixnum"
baseTyStr PositiveIntegerNotFixnum = "PositiveIntegerNotFixnum"
baseTyStr NegativeIntegerNotFixnum = "NegativeIntegerNotFixnum"
baseTyStr PositiveRationalNotInteger = "PositiveRationalNotInteger"
baseTyStr NegativeRationalNotInteger = "NegativeRationalNotInteger"
baseTyStr FloatNaN = "FloatNaN"
baseTyStr FloatPositiveZero = "FloatPositiveZero"
baseTyStr FloatNegativeZero = "FloatNegativeZero"
baseTyStr PositiveFloatNumber = "PositiveFloatNumber"
baseTyStr PositiveFloatInfinity = "PositiveFloatInfinity"
baseTyStr NegativeFloatNumber = "NegativeFloatNumber"
baseTyStr NegativeFloatInfinity = "NegativeFloatInfinity"
baseTyStr SingleFloatNaN = "SingleFloatNaN"
baseTyStr SingleFloatPositiveZero = "SingleFloatPositiveZero"
baseTyStr SingleFloatNegativeZero = "SingleFloatNegativeZero"
baseTyStr PositiveSingleFloatNumber = "PositiveSingleFloatNumber"
baseTyStr PositiveSingleFloatInfinity = "PositiveSingleFloatInfinity"
baseTyStr NegativeSingleFloatNumber = "NegativeSingleFloatNumber"
baseTyStr NegativeSingleFloatInfinity = "NegativeSingleFloatInfinity"
baseTyStr ExactImaginary = "ExactImaginary"
baseTyStr ExactComplex = "ExactComplex"
baseTyStr FloatImaginary = "FloatImaginary"
baseTyStr SingleFloatImaginary = "SingleFloatImaginary"
baseTyStr FloatComplex = "FloatComplex"
baseTyStr SingleFloatComplex = "SingleFloatComplex"

-- * * * * * * * * * * * * * * * * * * * * * * *
-- QuickCheck related definitions
-- * * * * * * * * * * * * * * * * * * * * * * *


instance Arbitrary Ty where
  arbitrary = sized arbitrarySizedTy
  shrink = shrinkTy

arbitrarySizedTy :: Int -> Gen Ty
arbitrarySizedTy n
  | n < 2 = frequency [(10, pure T)
                      ,(10, pure F)
                      ,(10, pure Zero)
                      ,(10, pure One)
                      ,(2, pure Any)
                      ,(1, pure Empty)]
  | otherwise = do
      t1 <- (arbitrarySizedTy n')
      t2 <- (arbitrarySizedTy n')
      t3 <- (arbitrarySizedTy n')
      frequency [(5, pure T)
                ,(5, pure F)
                ,(10, pure Zero)
                ,(10, pure One)
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
