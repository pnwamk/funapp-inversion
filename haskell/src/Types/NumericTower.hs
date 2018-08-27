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
zero = parseTy Stx.Zero
one = parseTy Stx.One
byteLargerThanOne = parseTy Stx.ByteLargerThanOne
positiveIndexNotByte = parseTy Stx.PositiveIndexNotByte
positiveFixnumNotIndex = parseTy Stx.PositiveFixnumNotIndex
negativeFixnum = parseTy Stx.NegativeFixnum
positiveIntegerNotFixnum = parseTy Stx.PositiveIntegerNotFixnum
negativeIntegerNotFixnum = parseTy Stx.NegativeIntegerNotFixnum
positiveRationalNotInteger = parseTy Stx.PositiveRationalNotInteger
negativeRationalNotInteger = parseTy Stx.NegativeRationalNotInteger
floatNaN = parseTy Stx.FloatNaN
floatPositiveZero = parseTy Stx.FloatPositiveZero
floatNegativeZero = parseTy Stx.FloatNegativeZero
positiveFloatNumber = parseTy Stx.PositiveFloatNumber
positiveFloatInfinity = parseTy Stx.PositiveFloatInfinity
negativeFloatNumber = parseTy Stx.NegativeFloatNumber
negativeFloatInfinity = parseTy Stx.NegativeFloatInfinity
singleFloatNaN = parseTy Stx.SingleFloatNaN
singleFloatPositiveZero = parseTy Stx.SingleFloatPositiveZero
singleFloatNegativeZero = parseTy Stx.SingleFloatNegativeZero
positiveSingleFloatNumber = parseTy Stx.PositiveSingleFloatNumber
positiveSingleFloatInfinity = parseTy Stx.PositiveSingleFloatInfinity
negativeSingleFloatNumber = parseTy Stx.NegativeSingleFloatNumber
negativeSingleFloatInfinity = parseTy Stx.NegativeSingleFloatInfinity
exactImaginary = parseTy Stx.ExactImaginary
exactComplex = parseTy Stx.ExactComplex
floatImaginary = parseTy Stx.FloatImaginary
singleFloatImaginary = parseTy Stx.SingleFloatImaginary
floatComplex = parseTy Stx.FloatComplex
singleFloatComplex = parseTy Stx.SingleFloatComplex

positiveByte = tyOr' [one, byteLargerThanOne]
byte = tyOr' [zero, positiveByte]

positiveIndex = tyOr' [one, byteLargerThanOne, positiveIndexNotByte]
index = tyOr' [zero, positiveIndex]

positiveFixnum = tyOr' [positiveFixnumNotIndex, positiveIndex]
nonnegativeFixnum = tyOr' [positiveFixnum, zero]

nonpositiveFixnum = tyOr' [negativeFixnum, zero]
fixnum = tyOr' [negativeFixnum, zero, positiveFixnum]
integerNotFixnum = tyOr' [negativeIntegerNotFixnum, positiveIntegerNotFixnum]
fixnumNotIndex = tyOr' [negativeFixnum, positiveFixnumNotIndex]

positiveInteger = tyOr' [positiveIntegerNotFixnum, positiveFixnum]
nonnegativeInteger = tyOr' [zero, positiveInteger]

negativeInteger = tyOr' [negativeFixnum, negativeIntegerNotFixnum]
nonpositiveInteger = tyOr' [negativeInteger, zero]
integer = tyOr' [negativeInteger, zero, positiveInteger]



positiveRational = tyOr' [positiveRationalNotInteger, positiveInteger]
nonnegativeRational = tyOr' [zero, positiveRational]

negativeRational = tyOr' [negativeRationalNotInteger, negativeInteger]
nonpositiveRational = tyOr' [negativeRational, zero]
rationalNotInteger = tyOr' [negativeRationalNotInteger, positiveRationalNotInteger]
rational = tyOr' [negativeRational, zero, positiveRational]

floatZero = tyOr' [floatPositiveZero, floatNegativeZero, floatNaN]
positiveFloat = tyOr' [positiveFloatNumber, positiveFloatInfinity, floatNaN]
nonnegativeFloat = tyOr' [positiveFloat, floatZero]
negativeFloat = tyOr' [negativeFloatNumber, negativeFloatInfinity, floatNaN]
nonpositiveFloat = tyOr' [negativeFloat, floatZero]
float = tyOr' [negativeFloatNumber,
            negativeFloatInfinity,
            floatNegativeZero,
            floatPositiveZero,
            positiveFloatNumber,
            positiveFloatInfinity,
            floatNaN]

singleFloatZero = tyOr' [singleFloatPositiveZero, singleFloatNegativeZero, singleFloatNaN]

inexactRealNaN = tyOr' [floatNaN, singleFloatNaN]
inexactRealPositiveZero = tyOr' [singleFloatPositiveZero, floatPositiveZero]
inexactRealNegativeZero = tyOr' [singleFloatNegativeZero, floatNegativeZero]
inexactRealZero = tyOr' [inexactRealPositiveZero,
                      inexactRealNegativeZero,
                      inexactRealNaN]

positiveSingleFloat = tyOr' [positiveSingleFloatNumber, positiveSingleFloatInfinity, singleFloatNaN]
positiveInexactReal = tyOr' [positiveSingleFloat, positiveFloat]
nonnegativeSingleFloat = tyOr' [positiveSingleFloat, singleFloatZero]
nonnegativeInexactReal = tyOr' [positiveInexactReal, inexactRealZero]
negativeSingleFloat = tyOr' [negativeSingleFloatNumber, negativeSingleFloatInfinity, singleFloatNaN]
negativeInexactReal = tyOr' [negativeSingleFloat, negativeFloat]
nonpositiveSingleFloat = tyOr' [negativeSingleFloat, singleFloatZero]
nonpositiveInexactReal = tyOr' [negativeInexactReal, inexactRealZero]
singleFloat = tyOr' [negativeSingleFloat,
                  singleFloatNegativeZero,
                  singleFloatPositiveZero,
                  positiveSingleFloat,
                  singleFloatNaN]
inexactReal = tyOr' [singleFloat, float]
positiveInfinity = tyOr' [positiveFloatInfinity, positiveSingleFloatInfinity]
negativeInfinity = tyOr' [negativeFloatInfinity, negativeSingleFloatInfinity]

realZero = tyOr' [zero, inexactRealZero]
realZeroNoNaN = tyOr' [zero, inexactRealPositiveZero, inexactRealNegativeZero]

positiveReal = tyOr' [positiveRational, positiveInexactReal]
nonnegativeReal = tyOr' [nonnegativeRational, nonnegativeInexactReal]
negativeReal = tyOr' [negativeRational, negativeInexactReal]
nonpositiveReal = tyOr' [nonpositiveRational, nonpositiveInexactReal]
real = tyOr' [rational, inexactReal]

exactNumber = tyOr' [exactImaginary, exactComplex, rational]
inexactImaginary = tyOr' [floatImaginary, singleFloatImaginary]
imaginary = tyOr' [exactImaginary, inexactImaginary]
inexactComplex = tyOr' [floatComplex, singleFloatComplex]
number = tyOr' [real, imaginary, exactComplex, inexactComplex]


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

nameMap :: Map.Map String Ty
nameMap = Map.fromList $
          numericTypes ++
          [ ("Any", anyTy)
          , ("Empty", emptyTy)
          , ("True", trueTy)
          , ("String", stringTy)
          , ("False", falseTy)
          , ("Boolean", boolTy)]

nameToTy :: String -> Maybe Ty
nameToTy name = Map.lookup name nameMap

realTypes :: [(String, Ty)]
realTypes = filter (\(_,t) -> subtype t real) numericTypes

-- types to help specify comparison types (i.e. signed types w/o NaN)
someNaN = tyOr' [singleFloatNaN, floatNaN]
positiveRealNoNaN = tyAnd' [positiveReal, (tyNot someNaN)]
nonnegativeRealNoNaN = tyAnd' [nonnegativeReal, (tyNot someNaN)]
negativeRealNoNaN = tyAnd' [negativeReal, (tyNot someNaN)]
nonpositiveRealNoNaN = tyAnd' [nonpositiveReal, (tyNot someNaN)]
realNoNaN = tyAnd' [real, (tyNot someNaN)]
positiveIntegerNotByte = tyAnd' [positiveInteger, (tyNot byte)]
positiveIntegerNotIndex = tyAnd' [positiveInteger, (tyNot index)]

