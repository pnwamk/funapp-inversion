module Types.SyntacticOpTypes
  ( 
  ) where

import Types.Syntax


incType :: [(Ty, Ty)]
incType = [ (zero, one)
          , (one, positiveByte)
          , (byte, positiveIndex)
          , (index, positiveFixnum)
          , (negativeFixnum, nonpositiveFixnum)
          , (nonpositiveFixnum, fixnum)
          , (nonnegativeInteger, positiveInteger)
          , (negativeInteger, nonpositiveInteger)
          , (integer, integer)
          , (nonnegativeRational, positiveRational)
          , (rational, rational)
          , (nonnegativeFloat, positiveFloat)
          , (float, float)
          , (nonnegativeSingleFloat, positiveSingleFloat)
          , (singleFloat, singleFloat)
          , (nonnegativeInexactReal, positiveInexactReal)
          , (inexactReal, inexactReal)
          , (nonnegativeReal, positiveReal)
          , (real, real)
          , (floatComplex, floatComplex)
          , (singleFloatComplex, singleFloatComplex)
          , (inexactComplex, inexactComplex)
          , (number, number)]

plusType :: [(Ty, Ty, Ty)]
plusType = [ (positiveByte, positiveByte, positiveIndex)
           , (byte, byte, index)
           , (positiveByte, positiveByte, positiveIndex)
           , (positiveIndex, index, positiveFixnum)
           , (index, positiveIndex, positiveFixnum)
           , (index, index, nonnegativeFixnum)
           , (negativeFixnum, one, nonpositiveFixnum)
           , (one, negativeFixnum, nonpositiveFixnum)
           , (nonpositiveFixnum, nonnegativeFixnum, fixnum)
           , (nonnegativeFixnum, nonpositiveFixnum, fixnum)
           , (positiveInteger, nonnegativeInteger, positiveInteger)
           , (nonnegativeInteger, positiveInteger, positiveInteger)
           , (negativeInteger, nonpositiveInteger, negativeInteger)
           , (nonpositiveInteger, negativeInteger, negativeInteger)
           , (nonnegativeInteger, nonnegativeInteger, nonnegativeInteger)
           , (nonpositiveInteger, nonpositiveInteger, nonpositiveInteger)
           , (integer, integer, integer)
           , (positiveRational, nonnegativeRational, positiveRational)
           , (nonnegativeRational, positiveRational, positiveRational)
           , (negativeRational, nonpositiveRational, negativeRational)
           , (nonpositiveRational, negativeRational, negativeRational)
           , (nonnegativeRational, nonnegativeRational, nonnegativeRational)
           , (nonpositiveRational, nonpositiveRational, nonpositiveRational)
           , (rational, rational, rational)
           , (positiveFloat, nonnegativeReal, positiveFloat)
           , (nonnegativeReal, positiveFloat, positiveFloat)
           , (positiveReal, nonnegativeFloat, positiveFloat)
           , (nonnegativeFloat, positiveReal, positiveFloat)
           , (negativeFloat, nonpositiveReal, negativeFloat)
           , (nonpositiveReal, negativeFloat, negativeFloat)
           , (negativeReal, nonpositiveFloat, negativeFloat)
           , (nonpositiveFloat, negativeReal, negativeFloat)
           , (nonnegativeFloat, nonnegativeReal, nonnegativeFloat)
           , (nonnegativeReal, nonnegativeFloat, nonnegativeFloat)
           , (nonpositiveFloat, nonpositiveReal, nonpositiveFloat)
           , (nonpositiveReal, nonpositiveFloat, nonpositiveFloat)
           , (float, real, float)
           , (real, float, float)
           , (float, float, float)
           , (positiveSingleFloat, (Or [nonnegativeRational, nonnegativeSingleFloat]), positiveSingleFloat)
           , ((Or [nonnegativeRational, nonnegativeSingleFloat]), positiveSingleFloat, positiveSingleFloat)
           , ((Or [positiveRational, positiveSingleFloat]), nonnegativeSingleFloat, positiveSingleFloat)
           , (nonnegativeSingleFloat, (Or [positiveRational, positiveSingleFloat]), positiveSingleFloat)
           , (negativeSingleFloat, (Or [nonpositiveRational, nonpositiveSingleFloat]), negativeSingleFloat)
           , ((Or [nonpositiveRational, nonpositiveSingleFloat]), negativeSingleFloat, negativeSingleFloat)
           , ((Or [negativeRational, negativeSingleFloat]), nonpositiveSingleFloat, negativeSingleFloat)
           , (nonpositiveSingleFloat, (Or [negativeRational, negativeSingleFloat]), negativeSingleFloat)
           , (nonnegativeSingleFloat, (Or [nonnegativeRational, nonnegativeSingleFloat]), nonnegativeSingleFloat)
           , ((Or [nonnegativeRational, nonnegativeSingleFloat]), nonnegativeSingleFloat, nonnegativeSingleFloat)
           , (nonpositiveSingleFloat, (Or [nonpositiveRational, nonpositiveSingleFloat]), nonpositiveSingleFloat)
           , ((Or [nonpositiveRational, nonpositiveSingleFloat]), nonpositiveSingleFloat, nonpositiveSingleFloat)
           , (singleFloat, (Or [rational, singleFloat]), singleFloat)
           , ((Or [rational, singleFloat]), singleFloat, singleFloat)
           , (singleFloat, singleFloat, singleFloat)
           , (positiveInexactReal, nonnegativeReal, positiveInexactReal)
           , (nonnegativeReal, positiveInexactReal, positiveInexactReal)
           , (positiveReal, nonnegativeInexactReal, positiveInexactReal)
           , (nonnegativeInexactReal, positiveReal, positiveInexactReal)
           , (negativeInexactReal, nonpositiveReal, negativeInexactReal)
           , (nonpositiveReal, negativeInexactReal, negativeInexactReal)
           , (negativeReal, nonpositiveInexactReal, negativeInexactReal)
           , (nonpositiveInexactReal, negativeReal, negativeInexactReal)
           , (nonnegativeInexactReal, nonnegativeReal, nonnegativeInexactReal)
           , (nonnegativeReal, nonnegativeInexactReal, nonnegativeInexactReal)
           , (nonpositiveInexactReal, nonpositiveReal, nonpositiveInexactReal)
           , (nonpositiveReal, nonpositiveInexactReal, nonpositiveInexactReal)
           , (inexactReal, real, inexactReal)
           , (real, inexactReal, inexactReal)
           , (positiveReal, nonnegativeReal, positiveReal)
           , (nonnegativeReal, positiveReal, positiveReal)
           , (negativeReal, nonpositiveReal, negativeReal)
           , (nonpositiveReal, negativeReal, negativeReal)
           , (nonnegativeReal, nonnegativeReal, nonnegativeReal)
           , (nonpositiveReal, nonpositiveReal, nonpositiveReal)
           , (real, real, real)
           , (exactNumber, exactNumber, exactNumber)
           , (floatComplex, number, floatComplex)
           , (number, floatComplex, floatComplex)
           , (float, inexactComplex, floatComplex)
           , (inexactComplex, float, floatComplex)
           , (singleFloatComplex, (Or [rational, singleFloat, singleFloatComplex]), singleFloatComplex)
           , ((Or [rational, singleFloat, singleFloatComplex]), singleFloatComplex, singleFloatComplex)
           , (inexactComplex, (Or [rational, inexactReal, inexactComplex]), inexactComplex)
           , ((Or [rational, inexactReal, inexactComplex]), inexactComplex, inexactComplex)
           , (number, number, number)]

ltType :: [(Ty, Ty, Prop, Prop)]
ltType = [ (integer, one, (IsA ArgZero nonpositiveInteger), (IsA ArgZero positiveInteger))
         , (real, zero, (IsA ArgZero negativeReal), (IsA ArgZero nonnegativeReal))
         , (zero, real, (IsA ArgOne positiveReal), (IsA ArgOne nonpositiveReal))
         , (real, realZero, (IsA ArgZero negativeReal), TT) -- False says nothing because of NaN
         , (realZero, real, (IsA ArgOne positiveReal), TT) -- False says nothing because of NaN
         , (byte, positiveByte, TT, (IsA ArgZero positiveByte))
         , (byte, byte, (IsA ArgOne positiveByte), TT)
         , (positiveInteger, byte, (Conj (IsA ArgZero positiveByte) (IsA ArgOne positiveByte)), TT)
         , (positiveReal, byte, (IsA ArgOne positiveByte), TT) -- positiveReal is ok here, no prop for #f
         , (byte, positiveInteger, TT, (Conj (IsA ArgZero positiveByte) (IsA ArgOne positiveByte)))
         , (byte, positiveRational, TT, (IsA ArgZero positiveByte)) -- can't be positiveReal, which includes NaN
         , (nonnegativeInteger, byte, (Conj (IsA ArgZero byte) (IsA ArgOne positiveByte)), TT)
         , (nonnegativeReal, byte, (IsA ArgOne positiveByte), TT)
         , (byte, nonnegativeInteger, TT, (IsA ArgOne byte))
         , (index, positiveIndex, TT, (IsA ArgZero positiveIndex))
         , (index, index, (IsA ArgOne positiveIndex), TT)
         , (positiveInteger, index, (Conj (IsA ArgZero positiveIndex) (IsA ArgOne positiveIndex)), TT)
         , (positiveReal, index, (IsA ArgOne positiveIndex), TT)
         , (index, positiveInteger, TT, (Conj (IsA ArgZero positiveIndex) (IsA ArgOne positiveIndex)))
         , (index, positiveRational, TT, (IsA ArgZero positiveIndex)) -- can't be positiveReal, which includes NaN
         , (nonnegativeInteger, index, (Conj (IsA ArgZero index) (IsA ArgOne positiveIndex)), TT)
         , (nonnegativeReal, index, (IsA ArgOne positiveIndex), TT)
         , (index, nonnegativeInteger, TT, (IsA ArgOne index))
         , (fixnum, positiveInteger, TT, (Conj (IsA ArgZero positiveFixnum) (IsA ArgOne positiveFixnum)))
         , (fixnum, positiveRational, TT, (IsA ArgZero positiveFixnum))
         , (fixnum, nonnegativeInteger, TT, (Conj (IsA ArgZero nonnegativeFixnum) (IsA ArgOne nonnegativeFixnum)))
         , (fixnum, nonnegativeRational, TT, (IsA ArgZero nonnegativeFixnum))
         , (nonnegativeInteger, fixnum, (Conj (IsA ArgZero nonnegativeFixnum) (IsA ArgOne positiveFixnum)), TT)
         , (nonnegativeReal, fixnum, (IsA ArgOne positiveFixnum), TT)
         , (fixnum, nonpositiveInteger, (Conj (IsA ArgZero negativeFixnum) (IsA ArgOne nonpositiveFixnum)), TT)
         , (fixnum, nonpositiveReal, (IsA ArgZero negativeFixnum), TT)
         , (negativeInteger, fixnum, TT, (Conj (IsA ArgZero negativeFixnum) (IsA ArgOne negativeFixnum)))
         , (negativeRational, fixnum, TT, (IsA ArgOne negativeFixnum))
         , (nonpositiveInteger, fixnum, TT, (Conj (IsA ArgZero nonpositiveFixnum) (IsA ArgOne nonpositiveFixnum)))
         , (nonpositiveRational, fixnum, TT, (IsA ArgOne nonpositiveFixnum))
         , (real, positiveInfinity,
            (IsA ArgZero (Not (Or [inexactRealNaN, positiveInfinity]))),
            (IsA ArgZero (Or [inexactRealNaN, positiveInfinity])))
         , (negativeInfinity, real,
            (IsA ArgOne (Not (Or [inexactRealNaN, negativeInfinity]))),
            (IsA ArgOne (Or [inexactRealNaN, negativeInfinity])))
         , (positiveInfinity, real, FF, TT)
         , (real, negativeInfinity, FF, TT)
         -- <-type-pattern integer
         , (integer, zero, (IsA ArgZero negativeInteger), (IsA ArgZero nonnegativeInteger))
         , (zero, integer, (IsA ArgOne positiveInteger), (IsA ArgOne nonpositiveInteger))
         , (integer, positiveReal, TT, (IsA ArgZero positiveInteger))
         , (integer, nonnegativeReal, TT, (IsA ArgZero nonnegativeInteger))
         , (nonnegativeReal, integer, (IsA ArgOne positiveInteger), TT)
         , (integer, nonpositiveReal, (IsA ArgZero negativeInteger), TT)
         , (negativeReal, integer, TT, (IsA ArgOne negativeInteger))
         , (nonpositiveReal, integer, TT, (IsA ArgOne nonpositiveInteger))
         -- <-type-pattern rational
         , (rational, zero, (IsA ArgZero negativeRational), (IsA ArgZero nonnegativeRational))
         , (zero, rational, (IsA ArgOne positiveRational), (IsA ArgOne nonpositiveRational))
         , (rational, positiveReal, TT, (IsA ArgZero positiveRational))
         , (rational, nonnegativeReal, TT, (IsA ArgZero nonnegativeRational))
         , (nonnegativeReal, rational, (IsA ArgOne positiveRational), TT)
         , (rational, nonpositiveReal, (IsA ArgZero negativeRational), TT)
         , (negativeReal, rational, TT, (IsA ArgOne negativeRational))
         , (nonpositiveReal, rational, TT, (IsA ArgOne nonpositiveRational))
         -- <-type-pattern float
         , (float, realZero, (IsA ArgZero negativeFloat), TT)
         , (realZero, float, (IsA ArgOne positiveFloat), TT)
         , (float, positiveReal, TT, TT)
         , (float, nonnegativeReal, TT, TT)
         , (nonnegativeReal, float, (IsA ArgOne positiveFloat), TT)
         , (float, nonpositiveReal, (IsA ArgZero negativeFloat), TT)
         , (negativeReal, float, TT, TT)
         , (nonpositiveReal, float, TT, TT)
         -- <-type-pattern single-Float
         , (singleFloat, realZero, (IsA ArgZero negativeSingleFloat), TT)
         , (realZero, singleFloat, (IsA ArgOne positiveSingleFloat), TT)
         , (singleFloat, positiveReal, TT, TT)
         , (singleFloat, nonnegativeReal, TT, TT)
         , (nonnegativeReal, singleFloat, (IsA ArgOne positiveSingleFloat), TT)
         , (singleFloat, nonpositiveReal, (IsA ArgZero negativeSingleFloat), TT)
         , (negativeReal, singleFloat, TT, TT)
         , (nonpositiveReal, singleFloat, TT, TT)
         -- <-type-pattern inexact-Real
         , (inexactReal, realZero, (IsA ArgZero negativeInexactReal), TT)
         , (realZero, inexactReal, (IsA ArgOne positiveInexactReal), TT)
         , (inexactReal, positiveReal, TT, TT)
         , (inexactReal, nonnegativeReal, TT, TT)
         , (nonnegativeReal, inexactReal, (IsA ArgOne positiveInexactReal), TT)
         , (inexactReal, nonpositiveReal, (IsA ArgZero negativeInexactReal), TT)
         , (negativeReal, inexactReal, TT, TT)
         , (nonpositiveReal, inexactReal, TT, TT)
         -- <-type-pattern real
         , (real, realZero, (IsA ArgZero negativeReal), TT)
         , (realZero, real, (IsA ArgOne positiveReal), TT)
         , (real, positiveReal, TT, TT)
         , (real, nonnegativeReal, TT, TT)
         , (nonnegativeReal, real, (IsA ArgOne positiveReal), TT)
         , (real, nonpositiveReal, (IsA ArgZero negativeReal), TT)
         , (negativeReal, real, TT, TT)
         , (nonpositiveReal, real, TT, TT)
         -- end of <-type-pattern
         , (real, real, TT, TT)]
