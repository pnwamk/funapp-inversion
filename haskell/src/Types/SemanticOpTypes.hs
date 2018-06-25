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
