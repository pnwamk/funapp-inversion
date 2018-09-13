module Types.BaseEnv where

import qualified Types.Syntax as Stx
import Types.LazyBDD
import Types.Subtype
import Data.Map (Map)
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
posIndexNotByte = parseTy mtEnv $ Stx.Base Stx.PosIndexNotByte
posFixnumNotIndex = parseTy mtEnv $ Stx.Base Stx.PosFixnumNotIndex
negFixnum = parseTy mtEnv $ Stx.Base Stx.NegFixnum
posIntegerNotFixnum = parseTy mtEnv $ Stx.Base Stx.PosIntegerNotFixnum
negIntegerNotFixnum = parseTy mtEnv $ Stx.Base Stx.NegIntegerNotFixnum
posRationalNotInteger = parseTy mtEnv $ Stx.Base Stx.PosRationalNotInteger
negRationalNotInteger = parseTy mtEnv $ Stx.Base Stx.NegRationalNotInteger
floatNaN = parseTy mtEnv $ Stx.Base Stx.FloatNaN
floatPosZero = parseTy mtEnv $ Stx.Base Stx.FloatPosZero
floatNegZero = parseTy mtEnv $ Stx.Base Stx.FloatNegZero
posFloatNumber = parseTy mtEnv $ Stx.Base Stx.PosFloatNumber
posFloatInfinity = parseTy mtEnv $ Stx.Base Stx.PosFloatInfinity
negFloatNumber = parseTy mtEnv $ Stx.Base Stx.NegFloatNumber
negFloatInfinity = parseTy mtEnv $ Stx.Base Stx.NegFloatInfinity
singleFloatNaN = parseTy mtEnv $ Stx.Base Stx.SingleFloatNaN
singleFloatPosZero = parseTy mtEnv $ Stx.Base Stx.SingleFloatPosZero
singleFloatNegZero = parseTy mtEnv $ Stx.Base Stx.SingleFloatNegZero
posSingleFloatNumber = parseTy mtEnv $ Stx.Base Stx.PosSingleFloatNumber
posSingleFloatInfinity = parseTy mtEnv $ Stx.Base Stx.PosSingleFloatInfinity
negSingleFloatNumber = parseTy mtEnv $ Stx.Base Stx.NegSingleFloatNumber
negSingleFloatInfinity = parseTy mtEnv $ Stx.Base Stx.NegSingleFloatInfinity
exactImaginary = parseTy mtEnv $ Stx.Base Stx.ExactImaginary
exactComplex = parseTy mtEnv $ Stx.Base Stx.ExactComplex
floatImaginary = parseTy mtEnv $ Stx.Base Stx.FloatImaginary
singleFloatImaginary = parseTy mtEnv $ Stx.Base Stx.SingleFloatImaginary
floatComplex = parseTy mtEnv $ Stx.Base Stx.FloatComplex
singleFloatComplex = parseTy mtEnv $ Stx.Base Stx.SingleFloatComplex

posByte = tyOr' [one, byteLargerThanOne]
byte = tyOr' [zero, posByte]
stxByte = Stx.Or [Stx.Base Stx.Zero,
                  Stx.Base Stx.One,
                  Stx.Base Stx.ByteLargerThanOne]

posIndex = tyOr' [one, byteLargerThanOne, posIndexNotByte]
index = tyOr' [zero, posIndex]

posFixnum = tyOr' [posFixnumNotIndex, posIndex]
nonnegFixnum = tyOr' [posFixnum, zero]

nonposFixnum = tyOr' [negFixnum, zero]
fixnum = tyOr' [negFixnum, zero, posFixnum]
integerNotFixnum = tyOr' [negIntegerNotFixnum, posIntegerNotFixnum]
fixnumNotIndex = tyOr' [negFixnum, posFixnumNotIndex]

posInteger = tyOr' [posIntegerNotFixnum, posFixnum]
nonnegInteger = tyOr' [zero, posInteger]

negInteger = tyOr' [negFixnum, negIntegerNotFixnum]
nonposInteger = tyOr' [negInteger, zero]
integer = tyOr' [negInteger, zero, posInteger]
stxInt = Stx.Or [ Stx.Base Stx.NegIntegerNotFixnum
                , Stx.Base Stx.NegFixnum
                , Stx.Base Stx.Zero
                , Stx.Base Stx.One
                , Stx.Base Stx.ByteLargerThanOne
                , Stx.Base Stx.PosIndexNotByte
                , Stx.Base Stx.PosFixnumNotIndex
                , Stx.Base Stx.PosIntegerNotFixnum]



posRational = tyOr' [posRationalNotInteger, posInteger]
nonnegRational = tyOr' [zero, posRational]

negRational = tyOr' [negRationalNotInteger, negInteger]
nonposRational = tyOr' [negRational, zero]
rationalNotInteger = tyOr' [negRationalNotInteger, posRationalNotInteger]
rational = tyOr' [negRational, zero, posRational]

floatZero = tyOr' [floatPosZero, floatNegZero, floatNaN]
posFloat = tyOr' [posFloatNumber, posFloatInfinity, floatNaN]
nonnegFloat = tyOr' [posFloat, floatZero]
negFloat = tyOr' [negFloatNumber, negFloatInfinity, floatNaN]
nonposFloat = tyOr' [negFloat, floatZero]
float = tyOr' [negFloatNumber,
            negFloatInfinity,
            floatNegZero,
            floatPosZero,
            posFloatNumber,
            posFloatInfinity,
            floatNaN]

singleFloatZero = tyOr' [singleFloatPosZero, singleFloatNegZero, singleFloatNaN]

inexactRealNaN = tyOr' [floatNaN, singleFloatNaN]
inexactRealPosZero = tyOr' [singleFloatPosZero, floatPosZero]
inexactRealNegZero = tyOr' [singleFloatNegZero, floatNegZero]
inexactRealZero = tyOr' [inexactRealPosZero,
                      inexactRealNegZero,
                      inexactRealNaN]

posSingleFloat = tyOr' [posSingleFloatNumber, posSingleFloatInfinity, singleFloatNaN]
posInexactReal = tyOr' [posSingleFloat, posFloat]
nonnegSingleFloat = tyOr' [posSingleFloat, singleFloatZero]
nonnegInexactReal = tyOr' [posInexactReal, inexactRealZero]
negSingleFloat = tyOr' [negSingleFloatNumber, negSingleFloatInfinity, singleFloatNaN]
negInexactReal = tyOr' [negSingleFloat, negFloat]
nonposSingleFloat = tyOr' [negSingleFloat, singleFloatZero]
nonposInexactReal = tyOr' [negInexactReal, inexactRealZero]
singleFloat = tyOr' [negSingleFloat,
                  singleFloatNegZero,
                  singleFloatPosZero,
                  posSingleFloat,
                  singleFloatNaN]
inexactReal = tyOr' [singleFloat, float]
posInfinity = tyOr' [posFloatInfinity, posSingleFloatInfinity]
negInfinity = tyOr' [negFloatInfinity, negSingleFloatInfinity]

realZero = tyOr' [zero, inexactRealZero]
realZeroNoNaN = tyOr' [zero, inexactRealPosZero, inexactRealNegZero]

posReal = tyOr' [posRational, posInexactReal]
nonnegReal = tyOr' [nonnegRational, nonnegInexactReal]
negReal = tyOr' [negRational, negInexactReal]
nonposReal = tyOr' [nonposRational, nonposInexactReal]
real = tyOr' [rational, inexactReal]

exactNumber = tyOr' [exactImaginary, exactComplex, rational]
inexactImaginary = tyOr' [floatImaginary, singleFloatImaginary]
imaginary = tyOr' [exactImaginary, inexactImaginary]
inexactComplex = tyOr' [floatComplex, singleFloatComplex]
number = tyOr' [real, imaginary, exactComplex, inexactComplex]
stxNum = Stx.Or [ Stx.Base Stx.Zero
                , Stx.Base Stx.One
                , Stx.Base Stx.ByteLargerThanOne
                , Stx.Base Stx.PosIndexNotByte
                , Stx.Base Stx.PosFixnumNotIndex
                , Stx.Base Stx.NegFixnum
                , Stx.Base Stx.PosIntegerNotFixnum
                , Stx.Base Stx.NegIntegerNotFixnum
                , Stx.Base Stx.PosRationalNotInteger
                , Stx.Base Stx.NegRationalNotInteger
                , Stx.Base Stx.FloatNaN
                , Stx.Base Stx.FloatPosZero
                , Stx.Base Stx.FloatNegZero
                , Stx.Base Stx.PosFloatNumber
                , Stx.Base Stx.PosFloatInfinity
                , Stx.Base Stx.NegFloatNumber
                , Stx.Base Stx.NegFloatInfinity
                , Stx.Base Stx.SingleFloatNaN
                , Stx.Base Stx.SingleFloatPosZero
                , Stx.Base Stx.SingleFloatNegZero
                , Stx.Base Stx.PosSingleFloatNumber
                , Stx.Base Stx.PosSingleFloatInfinity
                , Stx.Base Stx.NegSingleFloatNumber
                , Stx.Base Stx.NegSingleFloatInfinity
                , Stx.Base Stx.ExactImaginary
                , Stx.Base Stx.ExactComplex
                , Stx.Base Stx.FloatImaginary
                , Stx.Base Stx.SingleFloatImaginary
                , Stx.Base Stx.FloatComplex
                , Stx.Base Stx.SingleFloatComplex]

numericTypes :: [(String, Ty)]
numericTypes =
  [ ("Zero", zero)
  , ("One", one)
  , ("ByteLargerThanOne", byteLargerThanOne)
  , ("PosIndexNotByte", posIndexNotByte)
  , ("PosFixnumNotIndex", posFixnumNotIndex)
  , ("NegFixnum", negFixnum)
  , ("PosIntegerNotFixnum", posIntegerNotFixnum)
  , ("NegIntegerNotFixnum", negIntegerNotFixnum)
  , ("PosRationalNotInteger", posRationalNotInteger)
  , ("NegRationalNotInteger", negRationalNotInteger)
  , ("FloatNaN", floatNaN)
  , ("FloatPosZero", floatPosZero)
  , ("FloatNegZero", floatNegZero)
  , ("PosFloatNumber", posFloatNumber)
  , ("PosFloatInfinity", posFloatInfinity)
  , ("NegFloatNumber", negFloatNumber)
  , ("NegFloatInfinity", negFloatInfinity)
  , ("SingleFloatNaN", singleFloatNaN)
  , ("SingleFloatPosZero", singleFloatPosZero)
  , ("SingleFloatNegZero", singleFloatNegZero)
  , ("PosSingleFloatNumber", posSingleFloatNumber)
  , ("PosSingleFloatInfinity", posSingleFloatInfinity)
  , ("NegSingleFloatNumber", negSingleFloatNumber)
  , ("NegSingleFloatInfinity", negSingleFloatInfinity)
  , ("ExactImaginary", exactImaginary)
  , ("ExactComplex", exactComplex)
  , ("FloatImaginary", floatImaginary)
  , ("SingleFloatImaginary", singleFloatImaginary)
  , ("FloatComplex", floatComplex)
  , ("SingleFloatComplex", singleFloatComplex)
  , ("PosByte", posByte)
  , ("Byte", byte)
  , ("PosIndex", posIndex)
  , ("Index", index)
  , ("PosFixnum", posFixnum)
  , ("NonnegFixnum", nonnegFixnum)
  , ("NonposFixnum", nonposFixnum)
  , ("Fixnum", fixnum)
  , ("PosInteger", posInteger)
  , ("NonnegInteger", nonnegInteger)
  , ("NegInteger", negInteger)
  , ("NonposInteger", nonposInteger)
  , ("Integer", integer)
  , ("PosRational", posRational)
  , ("NonnegRational", nonnegRational)
  , ("NegRational", negRational)
  , ("NonposRational", nonposRational)
  , ("Rational", rational)
  , ("FloatZero", floatZero)
  , ("PosFloat", posFloat)
  , ("NonnegFloat", nonnegFloat)
  , ("NegFloat", negFloat)
  , ("NonposFloat", nonposFloat)
  , ("Float", float)
  , ("SingleFloatZero", singleFloatZero)
  , ("InexactRealNaN", inexactRealNaN)
  , ("InexactRealPosZero", inexactRealPosZero)
  , ("InexactRealNegZero", inexactRealNegZero)
  , ("InexactRealZero", inexactRealZero)
  , ("PosSingleFloat", posSingleFloat)
  , ("PosInexactReal", posInexactReal)
  , ("NonnegSingleFloat", nonnegSingleFloat)
  , ("NonnegInexactReal", nonnegInexactReal)
  , ("NegSingleFloat", negSingleFloat)
  , ("NegInexactReal", negInexactReal)
  , ("NonposSingleFloat", nonposSingleFloat)
  , ("NonposInexactReal", nonposInexactReal)
  , ("SingleFloat", singleFloat)
  , ("InexactReal", inexactReal)
  , ("PosInfinity", posInfinity)
  , ("NegInfinity", negInfinity)
  , ("RealZero", realZero)
  , ("RealZeroNoNaN", realZeroNoNaN)
  , ("PosReal", posReal)
  , ("NonnegReal", nonnegReal)
  , ("NegReal", negReal)
  , ("NonposReal", nonposReal)
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
          , ("Boolean", boolTy)
          , ("ByteList", parseTy baseEnv $
              Stx.Or [ Stx.Base Stx.Null
                     , Stx.Prod stxByte (Stx.Name "ByteList")])
          , ("IntList", parseTy baseEnv $
              Stx.Or [ Stx.Base Stx.Null
                     , Stx.Prod stxInt (Stx.Name "IntList")])
          , ("ZeroOneList", parseTy baseEnv $
            Stx.Or [ Stx.Base Stx.Null
                   , Stx.Prod (Stx.Base Stx.Zero) (Stx.Name "OneZeroList")])
          , ("OneZeroList", parseTy baseEnv $
            Stx.Or [ Stx.Base Stx.Null
                   , Stx.Prod (Stx.Base Stx.One) (Stx.Name "ZeroOneList")])
          , ("NumList", parseTy baseEnv $
              Stx.Or [ Stx.Base Stx.Null
                     , Stx.Prod stxNum (Stx.Name "NumList")])]

realTypes :: [(String, Ty)]
realTypes = filter (\(_,t) -> subtype t real) numericTypes

-- types to help specify comparison types (i.e. signed types w/o NaN)
someNaN = tyOr' [singleFloatNaN, floatNaN]
posRealNoNaN = tyAnd' [posReal, (tyNot someNaN)]
nonnegRealNoNaN = tyAnd' [nonnegReal, (tyNot someNaN)]
negRealNoNaN = tyAnd' [negReal, (tyNot someNaN)]
nonposRealNoNaN = tyAnd' [nonposReal, (tyNot someNaN)]
realNoNaN = tyAnd' [real, (tyNot someNaN)]
posIntegerNotByte = tyAnd' [posInteger, (tyNot byte)]
posIntegerNotIndex = tyAnd' [posInteger, (tyNot index)]

