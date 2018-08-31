module Types.NumericTower where

import qualified Types.Syntax as Stx
import Types.LazyBDD
import Types.Subtype
import qualified Data.Map as Map

data Obj = ArgZero | ArgOne
  deriving (Eq, Show, Ord)

data Prop =
    TT
  | FF
  | IsA Obj Ty
  | Conj Prop Prop
  deriving (Eq, Show, Ord)

data OpSpec =
    UnOp [(Ty, Ty)]
  | BinOp [(Ty, Ty, Ty)]
  | CompOp [(Ty, Ty, Prop ,Prop)]
  deriving (Eq, Show, Ord)



-- * * * * * * * * * * * * * * * * * * * * * * *
-- Common type definitions
-- * * * * * * * * * * * * * * * * * * * * * * *
zero = parseTy mtEnv $ Stx.Base Stx.Zero
one = parseTy mtEnv $ Stx.Base Stx.One
byteLargerThanOne = parseTy mtEnv $ Stx.Base Stx.ByteLargerThanOne
positiveIndexNotByte = parseTy mtEnv $ Stx.Base Stx.PositiveIndexNotByte
positiveFixnumNotIndex = parseTy mtEnv $ Stx.Base Stx.PositiveFixnumNotIndex
negativeFixnum = parseTy mtEnv $ Stx.Base Stx.NegativeFixnum
positiveIntegerNotFixnum = parseTy mtEnv $ Stx.Base Stx.PositiveIntegerNotFixnum
negativeIntegerNotFixnum = parseTy mtEnv $ Stx.Base Stx.NegativeIntegerNotFixnum
positiveRationalNotInteger = parseTy mtEnv $ Stx.Base Stx.PositiveRationalNotInteger
negativeRationalNotInteger = parseTy mtEnv $ Stx.Base Stx.NegativeRationalNotInteger
floatNaN = parseTy mtEnv $ Stx.Base Stx.FloatNaN
floatPositiveZero = parseTy mtEnv $ Stx.Base Stx.FloatPositiveZero
floatNegativeZero = parseTy mtEnv $ Stx.Base Stx.FloatNegativeZero
positiveFloatNumber = parseTy mtEnv $ Stx.Base Stx.PositiveFloatNumber
positiveFloatInfinity = parseTy mtEnv $ Stx.Base Stx.PositiveFloatInfinity
negativeFloatNumber = parseTy mtEnv $ Stx.Base Stx.NegativeFloatNumber
negativeFloatInfinity = parseTy mtEnv $ Stx.Base Stx.NegativeFloatInfinity
singleFloatNaN = parseTy mtEnv $ Stx.Base Stx.SingleFloatNaN
singleFloatPositiveZero = parseTy mtEnv $ Stx.Base Stx.SingleFloatPositiveZero
singleFloatNegativeZero = parseTy mtEnv $ Stx.Base Stx.SingleFloatNegativeZero
positiveSingleFloatNumber = parseTy mtEnv $ Stx.Base Stx.PositiveSingleFloatNumber
positiveSingleFloatInfinity = parseTy mtEnv $ Stx.Base Stx.PositiveSingleFloatInfinity
negativeSingleFloatNumber = parseTy mtEnv $ Stx.Base Stx.NegativeSingleFloatNumber
negativeSingleFloatInfinity = parseTy mtEnv $ Stx.Base Stx.NegativeSingleFloatInfinity
exactImaginary = parseTy mtEnv $ Stx.Base Stx.ExactImaginary
exactComplex = parseTy mtEnv $ Stx.Base Stx.ExactComplex
floatImaginary = parseTy mtEnv $ Stx.Base Stx.FloatImaginary
singleFloatImaginary = parseTy mtEnv $ Stx.Base Stx.SingleFloatImaginary
floatComplex = parseTy mtEnv $ Stx.Base Stx.FloatComplex
singleFloatComplex = parseTy mtEnv $ Stx.Base Stx.SingleFloatComplex

positiveByte = tyOr' mtEnv [one, byteLargerThanOne]
byte = tyOr' mtEnv [zero, positiveByte]

positiveIndex = tyOr' mtEnv [one, byteLargerThanOne, positiveIndexNotByte]
index = tyOr' mtEnv [zero, positiveIndex]

positiveFixnum = tyOr' mtEnv [positiveFixnumNotIndex, positiveIndex]
nonnegativeFixnum = tyOr' mtEnv [positiveFixnum, zero]

nonpositiveFixnum = tyOr' mtEnv [negativeFixnum, zero]
fixnum = tyOr' mtEnv [negativeFixnum, zero, positiveFixnum]
integerNotFixnum = tyOr' mtEnv [negativeIntegerNotFixnum, positiveIntegerNotFixnum]
fixnumNotIndex = tyOr' mtEnv [negativeFixnum, positiveFixnumNotIndex]

positiveInteger = tyOr' mtEnv [positiveIntegerNotFixnum, positiveFixnum]
nonnegativeInteger = tyOr' mtEnv [zero, positiveInteger]

negativeInteger = tyOr' mtEnv [negativeFixnum, negativeIntegerNotFixnum]
nonpositiveInteger = tyOr' mtEnv [negativeInteger, zero]
integer = tyOr' mtEnv [negativeInteger, zero, positiveInteger]



positiveRational = tyOr' mtEnv [positiveRationalNotInteger, positiveInteger]
nonnegativeRational = tyOr' mtEnv [zero, positiveRational]

negativeRational = tyOr' mtEnv [negativeRationalNotInteger, negativeInteger]
nonpositiveRational = tyOr' mtEnv [negativeRational, zero]
rationalNotInteger = tyOr' mtEnv [negativeRationalNotInteger, positiveRationalNotInteger]
rational = tyOr' mtEnv [negativeRational, zero, positiveRational]

floatZero = tyOr' mtEnv [floatPositiveZero, floatNegativeZero, floatNaN]
positiveFloat = tyOr' mtEnv [positiveFloatNumber, positiveFloatInfinity, floatNaN]
nonnegativeFloat = tyOr' mtEnv [positiveFloat, floatZero]
negativeFloat = tyOr' mtEnv [negativeFloatNumber, negativeFloatInfinity, floatNaN]
nonpositiveFloat = tyOr' mtEnv [negativeFloat, floatZero]
float = tyOr' mtEnv [negativeFloatNumber,
            negativeFloatInfinity,
            floatNegativeZero,
            floatPositiveZero,
            positiveFloatNumber,
            positiveFloatInfinity,
            floatNaN]

singleFloatZero = tyOr' mtEnv [singleFloatPositiveZero, singleFloatNegativeZero, singleFloatNaN]

inexactRealNaN = tyOr' mtEnv [floatNaN, singleFloatNaN]
inexactRealPositiveZero = tyOr' mtEnv [singleFloatPositiveZero, floatPositiveZero]
inexactRealNegativeZero = tyOr' mtEnv [singleFloatNegativeZero, floatNegativeZero]
inexactRealZero = tyOr' mtEnv [inexactRealPositiveZero,
                      inexactRealNegativeZero,
                      inexactRealNaN]

positiveSingleFloat = tyOr' mtEnv [positiveSingleFloatNumber, positiveSingleFloatInfinity, singleFloatNaN]
positiveInexactReal = tyOr' mtEnv [positiveSingleFloat, positiveFloat]
nonnegativeSingleFloat = tyOr' mtEnv [positiveSingleFloat, singleFloatZero]
nonnegativeInexactReal = tyOr' mtEnv [positiveInexactReal, inexactRealZero]
negativeSingleFloat = tyOr' mtEnv [negativeSingleFloatNumber, negativeSingleFloatInfinity, singleFloatNaN]
negativeInexactReal = tyOr' mtEnv [negativeSingleFloat, negativeFloat]
nonpositiveSingleFloat = tyOr' mtEnv [negativeSingleFloat, singleFloatZero]
nonpositiveInexactReal = tyOr' mtEnv [negativeInexactReal, inexactRealZero]
singleFloat = tyOr' mtEnv [negativeSingleFloat,
                  singleFloatNegativeZero,
                  singleFloatPositiveZero,
                  positiveSingleFloat,
                  singleFloatNaN]
inexactReal = tyOr' mtEnv [singleFloat, float]
positiveInfinity = tyOr' mtEnv [positiveFloatInfinity, positiveSingleFloatInfinity]
negativeInfinity = tyOr' mtEnv [negativeFloatInfinity, negativeSingleFloatInfinity]

realZero = tyOr' mtEnv [zero, inexactRealZero]
realZeroNoNaN = tyOr' mtEnv [zero, inexactRealPositiveZero, inexactRealNegativeZero]

positiveReal = tyOr' mtEnv [positiveRational, positiveInexactReal]
nonnegativeReal = tyOr' mtEnv [nonnegativeRational, nonnegativeInexactReal]
negativeReal = tyOr' mtEnv [negativeRational, negativeInexactReal]
nonpositiveReal = tyOr' mtEnv [nonpositiveRational, nonpositiveInexactReal]
real = tyOr' mtEnv [rational, inexactReal]

exactNumber = tyOr' mtEnv [exactImaginary, exactComplex, rational]
inexactImaginary = tyOr' mtEnv [floatImaginary, singleFloatImaginary]
imaginary = tyOr' mtEnv [exactImaginary, inexactImaginary]
inexactComplex = tyOr' mtEnv [floatComplex, singleFloatComplex]
number = tyOr' mtEnv [real, imaginary, exactComplex, inexactComplex]


numericTypes :: [(String, Ty)]
numericTypes =
  [ ("Zero", zero)
  , ("One", one)
  , ("ByteLargerThanOne", byteLargerThanOne)
  , ("PositiveIndexNotByte", positiveIndexNotByte)
  , ("PositiveFixnumNotIndex", positiveFixnumNotIndex)
  , ("NegativeFixnum", negativeFixnum)
  , ("PositiveIntegerNotFixnum", positiveIntegerNotFixnum)
  , ("NegativeIntegerNotFixnum", negativeIntegerNotFixnum)
  , ("PositiveRationalNotInteger", positiveRationalNotInteger)
  , ("NegativeRationalNotInteger", negativeRationalNotInteger)
  , ("FloatNaN", floatNaN)
  , ("FloatPositiveZero", floatPositiveZero)
  , ("FloatNegativeZero", floatNegativeZero)
  , ("PositiveFloatNumber", positiveFloatNumber)
  , ("PositiveFloatInfinity", positiveFloatInfinity)
  , ("NegativeFloatNumber", negativeFloatNumber)
  , ("NegativeFloatInfinity", negativeFloatInfinity)
  , ("SingleFloatNaN", singleFloatNaN)
  , ("SingleFloatPositiveZero", singleFloatPositiveZero)
  , ("SingleFloatNegativeZero", singleFloatNegativeZero)
  , ("PositiveSingleFloatNumber", positiveSingleFloatNumber)
  , ("PositiveSingleFloatInfinity", positiveSingleFloatInfinity)
  , ("NegativeSingleFloatNumber", negativeSingleFloatNumber)
  , ("NegativeSingleFloatInfinity", negativeSingleFloatInfinity)
  , ("ExactImaginary", exactImaginary)
  , ("ExactComplex", exactComplex)
  , ("FloatImaginary", floatImaginary)
  , ("SingleFloatImaginary", singleFloatImaginary)
  , ("FloatComplex", floatComplex)
  , ("SingleFloatComplex", singleFloatComplex)
  , ("PositiveByte", positiveByte)
  , ("Byte", byte)
  , ("PositiveIndex", positiveIndex)
  , ("Index", index)
  , ("PositiveFixnum", positiveFixnum)
  , ("NonnegativeFixnum", nonnegativeFixnum)
  , ("NonpositiveFixnum", nonpositiveFixnum)
  , ("Fixnum", fixnum)
  , ("PositiveInteger", positiveInteger)
  , ("NonnegativeInteger", nonnegativeInteger)
  , ("NegativeInteger", negativeInteger)
  , ("NonpositiveInteger", nonpositiveInteger)
  , ("Integer", integer)
  , ("PositiveRational", positiveRational)
  , ("NonnegativeRational", nonnegativeRational)
  , ("NegativeRational", negativeRational)
  , ("NonpositiveRational", nonpositiveRational)
  , ("Rational", rational)
  , ("FloatZero", floatZero)
  , ("PositiveFloat", positiveFloat)
  , ("NonnegativeFloat", nonnegativeFloat)
  , ("NegativeFloat", negativeFloat)
  , ("NonpositiveFloat", nonpositiveFloat)
  , ("Float", float)
  , ("SingleFloatZero", singleFloatZero)
  , ("InexactRealNaN", inexactRealNaN)
  , ("InexactRealPositiveZero", inexactRealPositiveZero)
  , ("InexactRealNegativeZero", inexactRealNegativeZero)
  , ("InexactRealZero", inexactRealZero)
  , ("PositiveSingleFloat", positiveSingleFloat)
  , ("PositiveInexactReal", positiveInexactReal)
  , ("NonnegativeSingleFloat", nonnegativeSingleFloat)
  , ("NonnegativeInexactReal", nonnegativeInexactReal)
  , ("NegativeSingleFloat", negativeSingleFloat)
  , ("NegativeInexactReal", negativeInexactReal)
  , ("NonpositiveSingleFloat", nonpositiveSingleFloat)
  , ("NonpositiveInexactReal", nonpositiveInexactReal)
  , ("SingleFloat", singleFloat)
  , ("InexactReal", inexactReal)
  , ("PositiveInfinity", positiveInfinity)
  , ("NegativeInfinity", negativeInfinity)
  , ("RealZero", realZero)
  , ("RealZeroNoNaN", realZeroNoNaN)
  , ("PositiveReal", positiveReal)
  , ("NonnegativeReal", nonnegativeReal)
  , ("NegativeReal", negativeReal)
  , ("NonpositiveReal", nonpositiveReal)
  , ("Real", real)
  , ("ExactNumber", exactNumber)
  , ("InexactImaginary", inexactImaginary)
  , ("Imaginary", imaginary)
  , ("InexactComplex", inexactComplex)
  , ("Number", number)]

baseEnv :: Env
baseEnv = Map.fromList $
          numericTypes ++
          [ ("Any", anyTy)
          , ("Empty", emptyTy)
          , ("True", trueTy)
          , ("String", stringTy)
          , ("Null", nullTy)
          , ("False", falseTy)
          , ("Boolean", boolTy)]

realTypes :: [(String, Ty)]
realTypes = filter (\(_,t) -> subtype mtEnv t real) numericTypes

-- types to help specify comparison types (i.e. signed types w/o NaN)
someNaN = tyOr' mtEnv [singleFloatNaN, floatNaN]
positiveRealNoNaN = tyAnd' mtEnv [positiveReal, (tyNot mtEnv someNaN)]
nonnegativeRealNoNaN = tyAnd' mtEnv [nonnegativeReal, (tyNot mtEnv someNaN)]
negativeRealNoNaN = tyAnd' mtEnv [negativeReal, (tyNot mtEnv someNaN)]
nonpositiveRealNoNaN = tyAnd' mtEnv [nonpositiveReal, (tyNot mtEnv someNaN)]
realNoNaN = tyAnd' mtEnv [real, (tyNot mtEnv someNaN)]
positiveIntegerNotByte = tyAnd' mtEnv [positiveInteger, (tyNot mtEnv byte)]
positiveIntegerNotIndex = tyAnd' mtEnv [positiveInteger, (tyNot mtEnv index)]

