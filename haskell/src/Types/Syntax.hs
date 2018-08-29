module Types.Syntax
  ( Ty(..)
  , Scope
  , abstract
  , instantiate
  , baseTypes
  , baseIndex
  , baseTyStr
  ) where

import Test.QuickCheck

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
  deriving (Eq, Show, Ord)
  

data Ty =
  | Base BaseTy
  | Prod Ty Ty
  | Arrow Ty Ty
  | Or [Ty]
  | And [Ty]
  | Not Ty
  | Any
  | Empty
  | Var String -- Type variable
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

baseTyStr :: BaseTy -> String
baseTyStr T = "True"
baseTyStr F = "False"
baseTyStr Str = "String"
baseTyStr t = show t

baseIndex :: BaseTy -> Int
baseIndex T                           = 0
baseIndex F                           = 1
baseIndex Str                         = 2
baseIndex Null                        = 3
baseIndex Zero                        = 4
baseIndex One                         = 5
baseIndex ByteLargerThanOne           = 6
baseIndex PositiveIndexNotByte        = 7
baseIndex PositiveFixnumNotIndex      = 8
baseIndex NegativeFixnum              = 9
baseIndex PositiveIntegerNotFixnum    = 10
baseIndex NegativeIntegerNotFixnum    = 11
baseIndex PositiveRationalNotInteger  = 12
baseIndex NegativeRationalNotInteger  = 13
baseIndex FloatNaN                    = 14
baseIndex FloatPositiveZero           = 15
baseIndex FloatNegativeZero           = 16
baseIndex PositiveFloatNumber         = 17
baseIndex PositiveFloatInfinity       = 18
baseIndex NegativeFloatNumber         = 19
baseIndex NegativeFloatInfinity       = 20
baseIndex SingleFloatNaN              = 21
baseIndex SingleFloatPositiveZero     = 22
baseIndex SingleFloatNegativeZero     = 23
baseIndex PositiveSingleFloatNumber   = 24
baseIndex PositiveSingleFloatInfinity = 25
baseIndex NegativeSingleFloatNumber   = 26
baseIndex NegativeSingleFloatInfinity = 27
baseIndex ExactImaginary              = 28
baseIndex ExactComplex                = 29
baseIndex FloatImaginary              = 30
baseIndex SingleFloatImaginary        = 31
baseIndex FloatComplex                = 32
baseIndex SingleFloatComplex          = 33

-- * * * * * * * * * * * * * * * * * * * * * * *
-- QuickCheck related definitions
-- * * * * * * * * * * * * * * * * * * * * * * *


instance Arbitrary Ty where
  arbitrary = sized arbitrarySizedTy
  shrink = shrinkTy

arbitrarySizedTy :: Int -> Gen Ty
arbitrarySizedTy n
  | n < 2 = frequency [(10, pure (Base T))
                      ,(10, pure (Base F))
                      ,(10, pure (Base Zero))
                      ,(10, pure (Base One))
                      ,(2, pure Any)
                      ,(1, pure Empty)]
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
