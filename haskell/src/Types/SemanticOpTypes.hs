module Types.SemanticOpTypes where

import Types.Syntax

incType :: [(Ty, Ty)]
incType = [ (zero, one)
          , (one, byte)
          , (byte, index)
          , (index, fixnum)
          , (integer, integer)
          , (rational, rational)
          , (float, float)
          , (singleFloat, singleFloat)
          , (floatComplex, floatComplex)
          , (singleFloatComplex, singleFloatComplex)
          , (nonnegativeReal, positiveReal)
          , (negativeFixnum, nonpositiveFixnum)
          , (negativeInteger, nonpositiveInteger)
          , (number, number)]

plusType :: [(Ty, Ty, Ty)]
plusType = [ (byte, byte, index)
           , (index, index, nonnegativeFixnum)
           , (negativeFixnum, one, nonpositiveFixnum)
           , (one, negativeFixnum, nonpositiveFixnum)
           , (nonpositiveFixnum, nonnegativeFixnum, fixnum)
           , (nonnegativeFixnum, nonpositiveFixnum, fixnum)
           , (integer, integer, integer)
           , (rational, rational, rational)
           , (float, real, float)
           , (real, float, float)
           , (singleFloat, (Or [rational, singleFloat]), singleFloat)
           , ((Or [rational, singleFloat]), singleFloat, singleFloat)
           , (exactNumber, exactNumber, exactNumber)
           , (floatComplex, number, floatComplex)
           , (number, floatComplex, floatComplex)
           , (float, inexactComplex, floatComplex)
           , (inexactComplex, float, floatComplex)
           , (singleFloatComplex, (Or [rational, singleFloat, singleFloatComplex]), singleFloatComplex)
           , ((Or [rational, singleFloat, singleFloatComplex]), singleFloatComplex, singleFloatComplex)
           , (number, number, number)
           , (nonnegativeReal, positiveReal, positiveReal)
           , (positiveReal, nonnegativeReal, positiveReal)
           , (negativeReal, nonpositiveReal, negativeReal)
           , (nonpositiveReal, negativeReal, negativeReal)
           , (nonnegativeReal, nonnegativeReal, nonnegativeReal)
           , (nonpositiveReal, nonpositiveReal, nonpositiveReal)]

-- types to help specify comparison types (i.e. signed types w/o NaN)
someNaN = Or [singleFloatNaN, floatNaN]
zeroNoNaN = And [realZero, (Not someNaN)]
positiveRealNoNaN = And [positiveReal, (Not someNaN)]
nonnegativeRealNoNaN = And [nonnegativeReal, (Not someNaN)]
negativeRealNoNaN = And [negativeReal, (Not someNaN)]
nonpositiveRealNoNaN = And [nonpositiveReal, (Not someNaN)]
realNoNaN = And [real, (Not someNaN)]
positiveIntegerNotByte = And [positiveInteger, (Not byte)]
positiveIntegerNotIndex = And [positiveInteger, (Not index)]


ltType :: [(Ty, Ty, Ty)]
ltType = [ -- general cases --
           -- -- -- -- -- -- -- -- --
           (realNoNaN, realNoNaN, bool)
         , (someNaN, real, F)
         , (real, someNaN, F)
           -- positive/nonpositive cases --
         , (nonpositiveRealNoNaN, positiveRealNoNaN, T)
         , (positiveRealNoNaN, nonpositiveRealNoNaN, F)
           -- zero/negative cases --
         , (negativeRealNoNaN, zeroNoNaN, T)
         , (zeroNoNaN, negativeRealNoNaN, F)
         -- bounded type cases --
         , (negativeInfinity, And [realNoNaN, (Not negativeInfinity)], T)
         , (realNoNaN, negativeInfinity, F)
         , (negativeIntegerNotFixnum, And [integer, (Not negativeIntegerNotFixnum)], T)
         , (And [integer, (Not negativeIntegerNotFixnum)], negativeIntegerNotFixnum, F)
         , (zeroNoNaN, zeroNoNaN, F)
         , (nonpositiveRealNoNaN, one, T)
         , (one, nonpositiveRealNoNaN, F)
         , (one, one, F)
         , (one, And[positiveInteger, (Not one)], T)
         , (And[positiveInteger, (Not one)], one, F)
         , (byte, positiveIntegerNotByte, T)
         , (positiveIntegerNotByte, byte, F)
         , (index, positiveIntegerNotIndex, T)
         , (positiveIntegerNotIndex, index, F)
         , (fixnum, positiveIntegerNotFixnum, T)
         , (positiveIntegerNotFixnum, fixnum, F)
         , (And [realNoNaN, (Not positiveInfinity)], positiveInfinity, T)
         , (positiveInfinity, realNoNaN, F)
         ]
