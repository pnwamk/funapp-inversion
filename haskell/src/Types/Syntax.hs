module Types.Syntax where

import Test.QuickCheck

-- Contains ASTs for set-theoretic types that are convenient
-- when writing tests and/or programs but are not designed
-- for efficient computation (see LazyBDD.hs for that)

data Ty =
  -- Base Types
  -- (Note: baseTypes below depends on these;
  --  modify baseTypes appropriately if these change)
    T
  | F
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

data Obj = ArgZero | ArgOne
  deriving (Eq, Show, Ord)

data Prop =
    TT
  | FF
  | IsA Obj Ty
  | Conj Prop Prop
  deriving (Eq, Show, Ord)

baseTypes :: [Ty]
baseTypes =
  [ T
  , F
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


-- * * * * * * * * * * * * * * * * * * * * * * *
-- Common type definitions
-- * * * * * * * * * * * * * * * * * * * * * * *
zero = Zero
one = One
byteLargerThanOne = ByteLargerThanOne
positiveIndexNotByte = PositiveIndexNotByte
positiveFixnumNotIndex = PositiveFixnumNotIndex
negativeFixnum = NegativeFixnum
positiveIntegerNotFixnum = PositiveIntegerNotFixnum
negativeIntegerNotFixnum = NegativeIntegerNotFixnum
positiveRationalNotInteger = PositiveRationalNotInteger
negativeRationalNotInteger = NegativeRationalNotInteger
floatNaN = FloatNaN
floatPositiveZero = FloatPositiveZero
floatNegativeZero = FloatNegativeZero
positiveFloatNumber = PositiveFloatNumber
positiveFloatInfinity = PositiveFloatInfinity
negativeFloatNumber = NegativeFloatNumber
negativeFloatInfinity = NegativeFloatInfinity
singleFloatNaN = SingleFloatNaN
singleFloatPositiveZero = SingleFloatPositiveZero
singleFloatNegativeZero = SingleFloatNegativeZero
positiveSingleFloatNumber = PositiveSingleFloatNumber
positiveSingleFloatInfinity = PositiveSingleFloatInfinity
negativeSingleFloatNumber = NegativeSingleFloatNumber
negativeSingleFloatInfinity = NegativeSingleFloatInfinity
exactImaginary = ExactImaginary
exactComplex = ExactComplex
floatImaginary = FloatImaginary
singleFloatImaginary = SingleFloatImaginary
floatComplex = FloatComplex
singleFloatComplex = SingleFloatComplex

bool = Or [T , F]

positiveByte = Or [one, byteLargerThanOne]
byte = Or [zero, positiveByte]

positiveIndex = Or [one, byteLargerThanOne, positiveIndexNotByte]
index = Or [zero, positiveIndex]

positiveFixnum = Or [positiveFixnumNotIndex, positiveIndex]
nonnegativeFixnum = Or [positiveFixnum, zero]

nonpositiveFixnum = Or [negativeFixnum, zero]
fixnum = Or [negativeFixnum, zero, positiveFixnum]

positiveInteger = Or [positiveIntegerNotFixnum, positiveFixnum]
nonnegativeInteger = Or [zero, positiveInteger]

negativeInteger = Or [negativeFixnum, negativeIntegerNotFixnum]
nonpositiveInteger = Or [negativeInteger, Zero]
integer = Or [negativeInteger, zero, positiveInteger]

positiveRational = Or [positiveRationalNotInteger, positiveInteger]
nonnegativeRational = Or [zero, positiveRational]

negativeRational = Or [negativeRationalNotInteger, negativeInteger]
nonpositiveRational = Or [negativeRational, zero]
rational = Or [negativeRational, zero, positiveRational]

floatZero = Or [floatPositiveZero, floatNegativeZero, floatNaN]
positiveFloat = Or [positiveFloatNumber, positiveFloatInfinity, floatNaN]
nonnegativeFloat = Or [positiveFloat, floatZero]
negativeFloat = Or [negativeFloatNumber, negativeFloatInfinity, floatNaN]
nonpositiveFloat = Or [negativeFloat, floatZero]
float = Or [negativeFloatNumber,
            negativeFloatInfinity,
            floatNegativeZero,
            floatPositiveZero,
            positiveFloatNumber,
            positiveFloatInfinity,
            floatNaN]

singleFloatZero = Or [singleFloatPositiveZero, singleFloatNegativeZero, singleFloatNaN]

inexactRealNaN = Or [floatNaN, singleFloatNaN]
inexactRealPositiveZero = Or [singleFloatPositiveZero, floatPositiveZero]
inexactRealNegativeZero = Or [singleFloatNegativeZero, floatNegativeZero]
inexactRealZero = Or [inexactRealPositiveZero,
                      inexactRealNegativeZero,
                      inexactRealNaN]

positiveSingleFloat = Or [positiveSingleFloatNumber, positiveSingleFloatInfinity, singleFloatNaN]
positiveInexactReal = Or [positiveSingleFloat, positiveFloat]
nonnegativeSingleFloat = Or [positiveSingleFloat, singleFloatZero]
nonnegativeInexactReal = Or [positiveInexactReal, inexactRealZero]
negativeSingleFloat = Or [negativeSingleFloatNumber, negativeSingleFloatInfinity, singleFloatNaN]
negativeInexactReal = Or [negativeSingleFloat, negativeFloat]
nonpositiveSingleFloat = Or [negativeSingleFloat, singleFloatZero]
nonpositiveInexactReal = Or [negativeInexactReal, inexactRealZero]
singleFloat = Or [negativeSingleFloat,
                  singleFloatNegativeZero,
                  singleFloatPositiveZero,
                  positiveSingleFloat,
                  singleFloatNaN]
inexactReal = Or [singleFloat, float]
positiveInfinity = Or [positiveFloatInfinity, positiveSingleFloatInfinity]
negativeInfinity = Or [negativeFloatInfinity, negativeSingleFloatInfinity]

realZero = Or [zero, inexactRealZero]
realZeroNoNaN = Or [zero, inexactRealPositiveZero, inexactRealNegativeZero]

positiveReal = Or [positiveRational, positiveInexactReal]
nonnegativeReal = Or [nonnegativeRational, nonnegativeInexactReal]
negativeReal = Or [negativeRational, negativeInexactReal]
nonpositiveReal = Or [nonpositiveRational, nonpositiveInexactReal]
real = Or [rational, inexactReal]

exactNumber = Or [exactImaginary, exactComplex, rational]
inexactImaginary = Or [floatImaginary, singleFloatImaginary]
imaginary = Or [exactImaginary, inexactImaginary]
inexactComplex = Or [floatComplex, singleFloatComplex]
number = Or [real, imaginary, exactComplex, inexactComplex]


numericTypes :: [(String, Ty)]
numericTypes =
  [ ("Zero", Zero)
  , ("One", One)
  , ("ByteLargerThanOne", ByteLargerThanOne)
  , ("PositiveIndexNotByte", PositiveIndexNotByte)
  , ("PositiveFixnumNotIndex", PositiveFixnumNotIndex)
  , ("NegativeFixnum", NegativeFixnum)
  , ("PositiveIntegerNotFixnum", PositiveIntegerNotFixnum)
  , ("NegativeIntegerNotFixnum", NegativeIntegerNotFixnum)
  , ("PositiveRationalNotInteger", PositiveRationalNotInteger)
  , ("NegativeRationalNotInteger", NegativeRationalNotInteger)
  , ("FloatNaN", FloatNaN)
  , ("FloatPositiveZero", FloatPositiveZero)
  , ("FloatNegativeZero", FloatNegativeZero)
  , ("PositiveFloatNumber", PositiveFloatNumber)
  , ("PositiveFloatInfinity", PositiveFloatInfinity)
  , ("NegativeFloatNumber", NegativeFloatNumber)
  , ("NegativeFloatInfinity", NegativeFloatInfinity)
  , ("SingleFloatNaN", SingleFloatNaN)
  , ("SingleFloatPositiveZero", SingleFloatPositiveZero)
  , ("SingleFloatNegativeZero", SingleFloatNegativeZero)
  , ("PositiveSingleFloatNumber", PositiveSingleFloatNumber)
  , ("PositiveSingleFloatInfinity", PositiveSingleFloatInfinity)
  , ("NegativeSingleFloatNumber", NegativeSingleFloatNumber)
  , ("NegativeSingleFloatInfinity", NegativeSingleFloatInfinity)
  , ("ExactImaginary", ExactImaginary)
  , ("ExactComplex", ExactComplex)
  , ("FloatImaginary", FloatImaginary)
  , ("SingleFloatImaginary", SingleFloatImaginary)
  , ("FloatComplex", FloatComplex)
  , ("SingleFloatComplex", SingleFloatComplex)
  , ("positiveByte", positiveByte)
  , ("byte", byte)
  , ("positiveIndex", positiveIndex)
  , ("index", index)
  , ("positiveFixnum", positiveFixnum)
  , ("nonnegativeFixnum", nonnegativeFixnum)
  , ("nonpositiveFixnum", nonpositiveFixnum)
  , ("fixnum", fixnum)
  , ("positiveInteger", positiveInteger)
  , ("nonnegativeInteger", nonnegativeInteger)
  , ("negativeInteger", negativeInteger)
  , ("nonpositiveInteger", nonpositiveInteger)
  , ("integer", integer)
  , ("positiveRational", positiveRational)
  , ("nonnegativeRational", nonnegativeRational)
  , ("negativeRational", negativeRational)
  , ("nonpositiveRational", nonpositiveRational)
  , ("rational", rational)
  , ("floatZero", floatZero)
  , ("positiveFloat", positiveFloat)
  , ("nonnegativeFloat", nonnegativeFloat)
  , ("negativeFloat", negativeFloat)
  , ("nonpositiveFloat", nonpositiveFloat)
  , ("float", float)
  , ("singleFloatZero", singleFloatZero)
  , ("inexactRealNaN", inexactRealNaN)
  , ("inexactRealPositiveZero", inexactRealPositiveZero)
  , ("inexactRealNegativeZero", inexactRealNegativeZero)
  , ("inexactRealZero", inexactRealZero)
  , ("positiveSingleFloat", positiveSingleFloat)
  , ("positiveInexactReal", positiveInexactReal)
  , ("nonnegativeSingleFloat", nonnegativeSingleFloat)
  , ("nonnegativeInexactReal", nonnegativeInexactReal)
  , ("negativeSingleFloat", negativeSingleFloat)
  , ("negativeInexactReal", negativeInexactReal)
  , ("nonpositiveSingleFloat", nonpositiveSingleFloat)
  , ("nonpositiveInexactReal", nonpositiveInexactReal)
  , ("singleFloat", singleFloat)
  , ("inexactReal", inexactReal)
  , ("positiveInfinity", positiveInfinity)
  , ("negativeInfinity", negativeInfinity)
  , ("realZero", realZero)
  , ("realZeroNoNaN", realZeroNoNaN)
  , ("positiveReal", positiveReal)
  , ("nonnegativeReal", nonnegativeReal)
  , ("negativeReal", negativeReal)
  , ("nonpositiveReal", nonpositiveReal)
  , ("real", real)
  , ("exactNumber", exactNumber)
  , ("inexactImaginary", inexactImaginary)
  , ("imaginary", imaginary)
  , ("inexactComplex", inexactComplex)
  , ("number", number)]


-- types to help specify comparison types (i.e. signed types w/o NaN)
someNaN = Or [singleFloatNaN, floatNaN]
positiveRealNoNaN = And [positiveReal, (Not someNaN)]
nonnegativeRealNoNaN = And [nonnegativeReal, (Not someNaN)]
negativeRealNoNaN = And [negativeReal, (Not someNaN)]
nonpositiveRealNoNaN = And [nonpositiveReal, (Not someNaN)]
realNoNaN = And [real, (Not someNaN)]
positiveIntegerNotByte = And [positiveInteger, (Not byte)]
positiveIntegerNotIndex = And [positiveInteger, (Not index)]



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
