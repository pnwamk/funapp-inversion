module Types.SyntacticOpTypes where

import Types.Syntax


opTypes :: [(String, OpSpec)]
opTypes =
  [ ("add1", (UnOp
              [ (zero, one)
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
              , (number, number)]))
    
  , ("sub1", (UnOp
              [ (one, zero)
              , (positiveByte, byte)
              , (positiveIndex, index)
              , (index, fixnum)
              , (positiveFixnum, nonnegativeFixnum)
              , (nonnegativeFixnum, fixnum)
              , (positiveInteger, nonnegativeInteger)
              , (nonpositiveInteger, negativeInteger)
              , (integer, integer)
              , (nonpositiveRational, negativeRational)
              , (rational, rational)
              , (nonpositiveFloat, negativeFloat)
              , (float, float)
              , (nonpositiveSingleFloat, negativeSingleFloat)
              , (singleFloat, singleFloat)
              , (nonpositiveInexactReal, negativeInexactReal)
              , (inexactReal, inexactReal)
              , (nonpositiveReal, negativeReal)
              , (real, real)
              , (floatComplex, floatComplex)
              , (singleFloatComplex, singleFloatComplex)
              , (inexactComplex, inexactComplex)
              , (number, number)]))
    
    --abs is not the identity on negative zeros.
  , ("abs", (UnOp
             [ (zero, zero)
             , (positiveReal, positiveReal)
             , (floatZero, floatZero) -- we know we at least get *some* zero, and that it preserves exactness
             , (singleFloatZero, singleFloatZero)
             , (realZero, realZero)
             , ((Or [positiveInteger, negativeInteger]), positiveInteger) -- abs not be closed on fixnums
             , (integer, nonnegativeInteger)
             , ((Or [positiveRational, negativeRational]), positiveRational)
             , (rational, nonnegativeRational)
             , ((Or [positiveFloat, negativeFloat]), positiveFloat)
             , (float, nonnegativeFloat)
             , ((Or [positiveSingleFloat, negativeSingleFloat]), positiveSingleFloat)
             , (singleFloat, nonnegativeSingleFloat)
             , ((Or [positiveInexactReal, negativeInexactReal]), positiveInexactReal)
             , (inexactReal, nonnegativeInexactReal)
             , ((Or [positiveReal, negativeReal]), positiveReal)
             , (real, nonnegativeReal)]))

  , ("+", (BinOp
            [ (positiveByte, positiveByte, positiveIndex)
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
            , (number, number, number)]))

  , ("-", (BinOp
            [ (zero, zero, zero)
            , (zero, positiveFixnum, negativeFixnum) -- half negation pattern
            , (zero, nonnegativeFixnum, nonpositiveFixnum) -- half negation pattern
            , (zero, positiveInteger, negativeInteger) -- negation pattern
            , (zero, nonnegativeInteger, nonpositiveInteger) -- negation pattern
            , (zero, negativeInteger, positiveInteger) -- negation pattern
            , (zero, nonpositiveInteger, nonnegativeInteger) -- negation pattern
            , (zero, positiveRational, negativeRational) -- negation pattern
            , (zero, nonnegativeRational, nonpositiveRational) -- negation pattern
            , (zero, negativeRational, positiveRational) -- negation pattern
            , (zero, nonpositiveRational, nonnegativeRational) -- negation pattern
            , (zero, positiveFloat, negativeFloat) -- negation pattern
            , (zero, nonnegativeFloat, nonpositiveFloat) -- negation pattern
            , (zero, negativeFloat, positiveFloat) -- negation pattern
            , (zero, nonpositiveFloat, nonnegativeFloat) -- negation pattern
            , (zero, positiveSingleFloat, negativeSingleFloat) -- negation pattern
            , (zero, nonnegativeSingleFloat, nonpositiveSingleFloat) -- negation pattern
            , (zero, negativeSingleFloat, positiveSingleFloat) -- negation pattern
            , (zero, nonpositiveSingleFloat, nonnegativeSingleFloat) -- negation pattern
            , (zero, positiveInexactReal, negativeInexactReal) -- negation pattern
            , (zero, nonnegativeInexactReal, nonpositiveInexactReal) -- negation pattern
            , (zero, negativeInexactReal, positiveInexactReal) -- negation pattern
            , (zero, nonpositiveInexactReal, nonnegativeInexactReal) -- negation pattern
            , (zero, positiveReal, negativeReal) -- negation pattern
            , (zero, nonnegativeReal, nonpositiveReal) -- negation pattern
            , (zero, negativeReal, positiveReal) -- negation pattern
            , (zero, nonpositiveReal, nonnegativeReal) -- negation pattern
            , (one, one, zero)
            , (positiveByte, one, byte)
            , (positiveIndex, one, index)
            , (positiveFixnum, one, nonnegativeFixnum)
            , (positiveInteger, one, nonnegativeInteger)
            , (nonnegativeFixnum, nonnegativeFixnum, fixnum)
            , (negativeFixnum, nonpositiveFixnum, fixnum)
            , (positiveInteger, nonpositiveInteger, positiveInteger)
            , (nonnegativeInteger, nonpositiveInteger, nonnegativeInteger)
            , (negativeInteger, nonnegativeInteger, negativeInteger)
            , (nonpositiveInteger, nonnegativeInteger, nonpositiveInteger)
            , (integer, integer, integer)
            , (positiveRational, nonpositiveRational, positiveRational)
            , (nonnegativeRational, nonpositiveRational, nonnegativeRational)
            , (negativeRational, nonnegativeRational, negativeRational)
            , (nonpositiveRational, nonnegativeRational, nonpositiveRational)
            , (rational, rational, rational)
            , (float, float, float)
            , (float, real, float)
            , (real, float, float)
            , (singleFloat, singleFloat, singleFloat)
            , (singleFloat, (Or [singleFloat, rational]), singleFloat)
            , ((Or [singleFloat, rational]), singleFloat, singleFloat)
            , (inexactReal, inexactReal, inexactReal)
            , (inexactReal, (Or [inexactReal, rational]), inexactReal)
            , ((Or [inexactReal, rational]), inexactReal, inexactReal)
            , (real, real, real)
            , (exactNumber, exactNumber, exactNumber)
            , (floatComplex, floatComplex, floatComplex)
            , (floatComplex, number, floatComplex)
            , (number, floatComplex, floatComplex)
            , (singleFloatComplex, singleFloatComplex, singleFloatComplex)
            , (singleFloatComplex, (Or [singleFloatComplex, exactNumber]), singleFloatComplex)
            , ((Or [singleFloatComplex, exactNumber]), singleFloatComplex, singleFloatComplex)
            , (inexactComplex, inexactComplex, inexactComplex)
            , (inexactComplex, (Or [inexactComplex, exactNumber]), inexactComplex)
            , ((Or [inexactComplex, exactNumber]), inexactComplex, inexactComplex)
            , (number, number, number)]))

  , ("*", (BinOp
            [ (zero, number, zero)
            , (number, zero, zero)
            , (positiveByte, positiveByte, positiveIndex)
            , (byte, byte, index)
            , (positiveInteger, positiveInteger, positiveInteger)
            , (nonnegativeInteger, nonnegativeInteger, nonnegativeInteger)
            , (negativeInteger, negativeInteger, positiveInteger)
            , (negativeInteger, positiveInteger, negativeInteger)
            , (positiveInteger, negativeInteger, negativeInteger)
            , (nonpositiveInteger, nonpositiveInteger, nonnegativeInteger)
            , (nonpositiveInteger, nonnegativeInteger, nonpositiveInteger)
            , (nonnegativeInteger, nonpositiveInteger, nonpositiveInteger)
            , (integer, integer, integer)
            , (positiveRational, positiveRational, positiveRational)
            , (nonnegativeRational, nonnegativeRational, nonnegativeRational)
            , (negativeRational, negativeRational, positiveRational)
            , (negativeRational, positiveRational, negativeRational)
            , (positiveRational, negativeRational, negativeRational)
            , (nonpositiveRational, nonpositiveRational, nonnegativeRational)
            , (nonpositiveRational, nonnegativeRational, nonpositiveRational)
            , (nonnegativeRational, nonpositiveRational, nonpositiveRational)
            , (rational, rational, rational)
            , (floatZero, floatZero, floatZero)
            , (nonnegativeFloat, nonnegativeFloat, nonnegativeFloat) -- ; no pos * -> pos (underflow)
            , (negativeFloat, negativeFloat, nonnegativeFloat) -- possible underflow, so no neg neg -> pos
            , (nonnegativeFloat, positiveReal, nonnegativeFloat) -- ; real args don't include 0
            , (positiveReal, nonnegativeFloat, nonnegativeFloat)
            , (float, (Or [positiveReal, negativeReal]), float)
            , ((Or [positiveReal, negativeReal]), float, float)
            , (float, float, float)
            , (singleFloatZero, singleFloatZero, singleFloatZero)
            , (nonnegativeSingleFloat, nonnegativeSingleFloat, nonnegativeSingleFloat)
            , (negativeSingleFloat, negativeSingleFloat, nonnegativeSingleFloat) -- ; possible underflow, so no neg neg -> pos
            , (nonnegativeSingleFloat, (Or [positiveRational, nonnegativeSingleFloat]), nonnegativeSingleFloat)
            , ((Or [positiveRational, nonnegativeSingleFloat]), nonnegativeSingleFloat, nonnegativeSingleFloat)
            , (singleFloat, (Or [positiveRational, negativeRational, singleFloat]), singleFloat)
            , ((Or [positiveRational, negativeRational, singleFloat]), singleFloat, singleFloat)
            , (singleFloat, singleFloat, singleFloat)
            , (inexactRealZero, inexactRealZero, inexactRealZero)
            , (nonnegativeInexactReal, nonnegativeInexactReal, nonnegativeInexactReal)
            , (negativeInexactReal, negativeInexactReal, nonnegativeInexactReal)
            , (nonnegativeInexactReal, (Or [positiveRational, nonnegativeInexactReal]), nonnegativeInexactReal)
            , ((Or [positiveRational, nonnegativeInexactReal]), nonnegativeInexactReal, nonnegativeInexactReal)
            , (inexactReal, (Or [positiveRational, negativeRational, inexactReal]), inexactReal)
            , ((Or [positiveRational, negativeRational, inexactReal]), inexactReal, inexactReal)
            , (inexactReal, inexactReal, inexactReal)
            , (nonnegativeReal, nonnegativeReal, nonnegativeReal) -- (* +inf.0 0.0) -> +nan.0
            , (nonpositiveReal, nonpositiveReal, nonnegativeReal)
            , (nonpositiveReal, nonnegativeReal, nonpositiveReal)
            , (nonnegativeReal, nonpositiveReal, nonpositiveReal)
            , (real, real, real)
            , (floatComplex, (Or [inexactComplex, inexactReal, positiveRational, negativeRational]), floatComplex)
            , ((Or [inexactComplex, inexactReal, positiveRational, negativeRational]), floatComplex, floatComplex)
            , (singleFloatComplex, (Or [singleFloatComplex, singleFloat, positiveRational, negativeRational]), singleFloatComplex)
            , ((Or [singleFloatComplex, singleFloat, positiveRational, negativeRational]), singleFloatComplex, singleFloatComplex)
            , (inexactComplex, (Or [inexactComplex, inexactReal, positiveRational, negativeRational]), inexactComplex)
            , ((Or [inexactComplex, inexactReal, positiveRational, negativeRational]), inexactComplex, inexactComplex)
            , (number, number, number)]))

  , ("/", (BinOp
            [ (number, zero, Empty)
            , (zero, number, zero)
            , (one, one, one)
            , (positiveRational, positiveRational, positiveRational)
            , (nonnegativeRational, nonnegativeRational, nonnegativeRational)
            , (negativeRational, negativeRational, positiveRational)
            , (negativeRational, positiveRational, negativeRational)
            , (positiveRational, negativeRational, negativeRational)
            , (nonpositiveRational, nonpositiveRational, nonnegativeRational)
            , (nonpositiveRational, nonnegativeRational, nonpositiveRational)
            , (nonnegativeRational, nonpositiveRational, nonpositiveRational)
            , (rational, rational, rational)
            , (negativeFloat, negativeFloat, nonnegativeFloat)
            , (positiveFloat, positiveReal, nonnegativeFloat)
            , (positiveReal, positiveFloat, nonnegativeFloat)
            , ((Or [positiveReal, negativeReal, float]), float, float)
            , (float, real, float) -- if any argument after the first is exact 0, not a problem
            , (float, float, float)
            , (negativeSingleFloat, negativeSingleFloat, nonnegativeSingleFloat) -- possible underflow, so no neg neg -> pos
            , (positiveSingleFloat, (Or [positiveRational, positiveSingleFloat]), nonnegativeSingleFloat)
            , ((Or [positiveRational, positiveSingleFloat]), positiveSingleFloat, nonnegativeSingleFloat)
            , (singleFloat, (Or [positiveRational, negativeRational, singleFloat]), singleFloat)
            , ((Or [positiveRational, negativeRational, singleFloat]), singleFloat, singleFloat)
            , (singleFloat, singleFloat, singleFloat)
            , (negativeInexactReal, negativeInexactReal, nonnegativeInexactReal)
            , (positiveInexactReal, (Or [positiveRational, positiveInexactReal]), nonnegativeInexactReal)
            , ((Or [positiveRational, positiveInexactReal]), positiveInexactReal, nonnegativeInexactReal)
            , (inexactReal, (Or [positiveRational, negativeRational, inexactReal]), inexactReal)
            , ((Or [positiveRational, negativeRational, inexactReal]), inexactReal, inexactReal)
            , (inexactReal, inexactReal, inexactReal)
            , (positiveReal, positiveReal, nonnegativeReal)
            , (negativeReal, negativeReal, nonnegativeReal) -- 0.0 is non-neg, but doesn't preserve sign
            , (negativeReal, positiveReal, nonpositiveReal) -- idem
            , (positiveReal, negativeReal, nonpositiveReal) -- idem
            , (real, real, real)
            , (floatComplex, floatComplex, floatComplex)
            , (floatComplex, (Or [inexactComplex, inexactReal, positiveRational, negativeRational]), floatComplex)
            , ((Or [inexactComplex, inexactReal, positiveRational, negativeRational]), floatComplex, floatComplex)
            , (floatComplex, number, floatComplex) -- if any argument after the first is exact 0, not a problem
            , (singleFloatComplex, singleFloatComplex, singleFloatComplex)
            , (singleFloatComplex, (Or [singleFloatComplex, singleFloat, positiveRational, negativeRational]), singleFloatComplex)
            , ((Or [singleFloatComplex, singleFloat, positiveRational, negativeRational]), singleFloatComplex, singleFloatComplex)
            , (inexactComplex, inexactComplex, inexactComplex)
            , (inexactComplex, (Or [inexactComplex, inexactReal, positiveRational, negativeRational]), inexactComplex)
            , ((Or [inexactComplex, inexactReal, positiveRational, negativeRational]), inexactComplex, inexactComplex)
            , (number, number, number)]))

  , ("max", (BinOp
              [ (zero, zero, zero)
              , (one, one, one)
              , (one, zero, one)
              , (zero, one, one)
              , (positiveByte, byte, positiveByte)
              , (byte, positiveByte, positiveByte)
              , (positiveIndex, index, positiveIndex)
              , (index, positiveIndex, positiveIndex)
              , (positiveFixnum, fixnum, positiveFixnum)
              , (fixnum, positiveFixnum, positiveFixnum)
              , (nonnegativeFixnum, fixnum, nonnegativeFixnum)
              , (fixnum, nonnegativeFixnum, nonnegativeFixnum)
              , (index, index, index)
              , (negativeFixnum, negativeFixnum, negativeFixnum)
              , (nonpositiveFixnum, nonpositiveFixnum, nonpositiveFixnum)
              , (positiveFixnum, positiveFixnum, positiveFixnum)
              , (nonnegativeFixnum, nonnegativeFixnum, nonnegativeFixnum)
              , (fixnum, fixnum, fixnum)
              , (positiveInteger, integer, positiveInteger)
              , (integer, positiveInteger, positiveInteger)
              , (nonnegativeInteger, integer, nonnegativeInteger)
              , (integer, nonnegativeInteger, nonnegativeInteger)
              , (negativeInteger, negativeInteger, negativeInteger)
              , (nonpositiveInteger, nonpositiveInteger, nonpositiveInteger)
              , (positiveInteger, positiveInteger, positiveInteger)
              , (nonnegativeInteger, nonnegativeInteger, nonnegativeInteger)
              , (integer, integer, integer)
              , (positiveRational, rational, positiveRational)
              , (rational, positiveRational, positiveRational)
              , (nonnegativeRational, rational, nonnegativeRational)
              , (rational, nonnegativeRational, nonnegativeRational)
              , (negativeRational, negativeRational, negativeRational)
              , (nonpositiveRational, nonpositiveRational, nonpositiveRational)
              , (positiveRational, positiveRational, positiveRational)
              , (nonnegativeRational, nonnegativeRational, nonnegativeRational)
              , (rational, rational, rational)
              , (floatPositiveZero, floatPositiveZero, floatPositiveZero)
              , (floatNegativeZero, floatNegativeZero, floatNegativeZero)
              , (floatZero, floatZero, floatZero)
              , (positiveFloat, float, positiveFloat)
              , (float, positiveFloat, positiveFloat)
              , (nonnegativeFloat, float, nonnegativeFloat)
              , (float, nonnegativeFloat, nonnegativeFloat)
              , (negativeFloat, negativeFloat, negativeFloat)
              , (nonpositiveFloat, nonpositiveFloat, nonpositiveFloat)
              , (positiveFloat, positiveFloat, positiveFloat)
              , (nonnegativeFloat, nonnegativeFloat, nonnegativeFloat)
              , (float, float, float)
              , (singleFloatPositiveZero, singleFloatPositiveZero, singleFloatPositiveZero)
              , (singleFloatNegativeZero, singleFloatNegativeZero, singleFloatNegativeZero)
              , (singleFloatZero, singleFloatZero, singleFloatZero)
              , (positiveSingleFloat, positiveSingleFloat, positiveSingleFloat)
              , (positiveSingleFloat, singleFloat, positiveSingleFloat)
              , (singleFloat, positiveSingleFloat, positiveSingleFloat)
              , (nonnegativeSingleFloat, nonnegativeSingleFloat, nonnegativeSingleFloat)
              , (nonnegativeSingleFloat, singleFloat, nonnegativeSingleFloat)
              , (singleFloat, nonnegativeSingleFloat, nonnegativeSingleFloat)
              , (negativeSingleFloat, negativeSingleFloat, negativeSingleFloat)
              , (nonpositiveSingleFloat, nonpositiveSingleFloat, nonpositiveSingleFloat)
              , (singleFloat, singleFloat, singleFloat)
              , (inexactRealPositiveZero, inexactRealPositiveZero, inexactRealPositiveZero)
              , (inexactRealNegativeZero, inexactRealNegativeZero, inexactRealNegativeZero)
              , (inexactRealZero, inexactRealZero, inexactRealZero)
              , (positiveInexactReal, inexactReal, positiveInexactReal)
              , (inexactReal, positiveInexactReal, positiveInexactReal)
              , (nonnegativeInexactReal, inexactReal, nonnegativeInexactReal)
              , (inexactReal, nonnegativeInexactReal, nonnegativeInexactReal)
              , (negativeInexactReal, negativeInexactReal, negativeInexactReal)
              , (nonpositiveInexactReal, nonpositiveInexactReal, nonpositiveInexactReal)
              , (positiveInexactReal, positiveInexactReal, positiveInexactReal)
              , (nonnegativeInexactReal, nonnegativeInexactReal, nonnegativeInexactReal)
              , (inexactReal, inexactReal, inexactReal)
              , (realZero, realZero, realZero)
              , (positiveReal, real, positiveReal)
              , (real, positiveReal, positiveReal)
              , (nonnegativeReal, real, nonnegativeReal)
              , (real, nonnegativeReal, nonnegativeReal)
              , (negativeReal, negativeReal, negativeReal)
              , (nonpositiveReal, nonpositiveReal, nonpositiveReal)
              , (positiveReal, positiveReal, positiveReal)
              , (nonnegativeReal, nonnegativeReal, nonnegativeReal)
              , (real, real, real)]))

  , ("min", (BinOp
              [ (zero, zero, zero)
              , (one, one, one)
              , (zero, one, zero)
              , (one, zero, zero)
              , (positiveByte, positiveByte, positiveByte)
              , (byte, byte, byte)
              , (positiveIndex, positiveIndex, positiveIndex)
              , (index, index, index)
              , (positiveFixnum, positiveFixnum, positiveFixnum)
              , (nonnegativeFixnum, nonnegativeFixnum, nonnegativeFixnum)
              , (negativeFixnum, fixnum, negativeFixnum)
              , (fixnum, negativeFixnum, negativeFixnum)
              , (nonpositiveFixnum, fixnum, nonpositiveFixnum)
              , (fixnum, nonpositiveFixnum, nonpositiveFixnum)
              , (positiveByte, positiveInteger, positiveByte)
              , (positiveInteger, positiveByte, positiveByte)
              , (byte, nonnegativeInteger, byte)
              , (nonnegativeInteger, byte, byte)
              , (positiveFixnum, positiveInteger, positiveFixnum)
              , (positiveInteger, positiveFixnum, positiveFixnum)
              , (nonnegativeFixnum, nonnegativeInteger, nonnegativeFixnum)
              , (nonnegativeInteger, nonnegativeFixnum, nonnegativeFixnum)
              , (negativeFixnum, negativeFixnum, negativeFixnum)
              , (nonpositiveFixnum, nonpositiveFixnum, nonpositiveFixnum)
              , (fixnum, fixnum, fixnum)
              , (positiveInteger, positiveInteger, positiveInteger)
              , (nonnegativeInteger, nonnegativeInteger, nonnegativeInteger)
              , (negativeInteger, integer, negativeInteger)
              , (integer, negativeInteger, negativeInteger)
              , (nonpositiveInteger, integer, nonpositiveInteger)
              , (integer, nonpositiveInteger, nonpositiveInteger)
              , (negativeInteger, negativeInteger, negativeInteger)
              , (nonpositiveInteger, nonpositiveInteger, nonpositiveInteger)
              , (integer, integer, integer)
              , (positiveRational, positiveRational, positiveRational)
              , (nonnegativeRational, nonnegativeRational, nonnegativeRational)
              , (negativeRational, rational, negativeRational)
              , (rational, negativeRational, negativeRational)
              , (nonpositiveRational, rational, nonpositiveRational)
              , (rational, nonpositiveRational, nonpositiveRational)
              , (negativeRational, negativeRational, negativeRational)
              , (nonpositiveRational, nonpositiveRational, nonpositiveRational)
              , (rational, rational, rational)
              , (floatPositiveZero, floatPositiveZero, floatPositiveZero)
              , (floatNegativeZero, floatNegativeZero, floatNegativeZero)
              , (floatZero, floatZero, floatZero)
              , (positiveFloat, positiveFloat, positiveFloat)
              , (nonnegativeFloat, nonnegativeFloat, nonnegativeFloat)
              , (negativeFloat, float, negativeFloat)
              , (float, negativeFloat, negativeFloat)
              , (nonpositiveFloat, float, nonpositiveFloat)
              , (float, nonpositiveFloat, nonpositiveFloat)
              , (negativeFloat, negativeFloat, negativeFloat)
              , (nonpositiveFloat, nonpositiveFloat, nonpositiveFloat)
              , (float, float, float)
              , (singleFloatPositiveZero, singleFloatPositiveZero, singleFloatPositiveZero)
              , (singleFloatNegativeZero, singleFloatNegativeZero, singleFloatNegativeZero)
              , (singleFloatZero, singleFloatZero, singleFloatZero)
              , (positiveSingleFloat, positiveSingleFloat, positiveSingleFloat)
              , (nonnegativeSingleFloat, nonnegativeSingleFloat, nonnegativeSingleFloat)
              , (negativeSingleFloat, singleFloat, negativeSingleFloat)
              , (singleFloat, negativeSingleFloat, negativeSingleFloat)
              , (nonpositiveSingleFloat, singleFloat, nonpositiveSingleFloat)
              , (singleFloat, nonpositiveSingleFloat, nonpositiveSingleFloat)
              , (negativeSingleFloat, negativeSingleFloat, negativeSingleFloat)
              , (nonpositiveSingleFloat, nonpositiveSingleFloat, nonpositiveSingleFloat)
              , (singleFloat, singleFloat, singleFloat)
              , (inexactRealPositiveZero, inexactRealPositiveZero, inexactRealPositiveZero)
              , (inexactRealNegativeZero, inexactRealNegativeZero, inexactRealNegativeZero)
              , (inexactRealZero, inexactRealZero, inexactRealZero)
              , (positiveInexactReal, positiveInexactReal, positiveInexactReal)
              , (nonnegativeInexactReal, nonnegativeInexactReal, nonnegativeInexactReal)
              , (negativeInexactReal, inexactReal, negativeInexactReal)
              , (inexactReal, negativeInexactReal, negativeInexactReal)
              , (nonpositiveInexactReal, inexactReal, nonpositiveInexactReal)
              , (inexactReal, nonpositiveInexactReal, nonpositiveInexactReal)
              , (negativeInexactReal, negativeInexactReal, negativeInexactReal)
              , (nonpositiveInexactReal, nonpositiveInexactReal, nonpositiveInexactReal)
              , (inexactReal, inexactReal, inexactReal)
              , (realZero, realZero, realZero)
              , (positiveReal, positiveReal, positiveReal)
              , (nonnegativeReal, nonnegativeReal, nonnegativeReal)
              , (negativeReal, real, negativeReal)
              , (real, negativeReal, negativeReal)
              , (nonpositiveReal, real, nonpositiveReal)
              , (real, nonpositiveReal, nonpositiveReal)
              , (negativeReal, negativeReal, negativeReal)
              , (nonpositiveReal, nonpositiveReal, nonpositiveReal)
              , (real, real, real)]))

  , ("<", (CompOp
           [ (integer, one, (IsA ArgZero nonpositiveInteger), (IsA ArgZero positiveInteger))
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
           , (real, positiveInfinity, (IsA ArgZero (Not (Or [inexactRealNaN, positiveInfinity]))), (IsA ArgZero (Or [inexactRealNaN, positiveInfinity])))
           , (negativeInfinity, real, (IsA ArgOne (Not (Or [inexactRealNaN, negativeInfinity]))), (IsA ArgOne (Or [inexactRealNaN, negativeInfinity])))
           , (positiveInfinity, real, FF, TT)
           , (real, negativeInfinity, FF, TT)
           , (integer, zero, (IsA ArgZero negativeInteger), (IsA ArgZero nonnegativeInteger)) -- <-type-pattern integer
           , (zero, integer, (IsA ArgOne positiveInteger), (IsA ArgOne nonpositiveInteger))
           , (integer, positiveRealNoNaN, TT, (IsA ArgZero positiveInteger)) -- AMK added NoNaN
           , (integer, nonnegativeRealNoNaN, TT, (IsA ArgZero nonnegativeInteger)) -- AMK added NoNaN
           , (nonnegativeReal, integer, (IsA ArgOne positiveInteger), TT)
           , (integer, nonpositiveReal, (IsA ArgZero negativeInteger), TT)
           , (negativeRealNoNaN, integer, TT, (IsA ArgOne negativeInteger)) -- AMK added NoNaN
           , (nonpositiveRealNoNaN, integer, TT, (IsA ArgOne nonpositiveInteger)) -- AMK added NoNaN
           , (rational, zero, (IsA ArgZero negativeRational), (IsA ArgZero nonnegativeRational)) -- <-type-pattern rational
           , (zero, rational, (IsA ArgOne positiveRational), (IsA ArgOne nonpositiveRational))
           , (rational, positiveRealNoNaN, TT, (IsA ArgZero positiveRational)) -- AMK added NoNaN
           , (rational, nonnegativeRealNoNaN, TT, (IsA ArgZero nonnegativeRational)) -- AMK added NoNaN
           , (nonnegativeReal, rational, (IsA ArgOne positiveRational), TT)
           , (rational, nonpositiveReal, (IsA ArgZero negativeRational), TT)
           , (negativeRealNoNaN, rational, TT, (IsA ArgOne negativeRational)) -- AMK added NoNaN
           , (nonpositiveRealNoNaN, rational, TT, (IsA ArgOne nonpositiveRational)) -- AMK added NoNaN
           , (float, realZero, (IsA ArgZero negativeFloat), TT) -- <-type-pattern float
           , (realZero, float, (IsA ArgOne positiveFloat), TT)
           , (float, positiveReal, TT, TT)
           , (float, nonnegativeReal, TT, TT)
           , (nonnegativeReal, float, (IsA ArgOne positiveFloat), TT)
           , (float, nonpositiveReal, (IsA ArgZero negativeFloat), TT)
           , (negativeReal, float, TT, TT)
           , (nonpositiveReal, float, TT, TT)
           , (singleFloat, realZero, (IsA ArgZero negativeSingleFloat), TT) -- <-type-pattern single-Float
           , (realZero, singleFloat, (IsA ArgOne positiveSingleFloat), TT)
           , (singleFloat, positiveReal, TT, TT)
           , (singleFloat, nonnegativeReal, TT, TT)
           , (nonnegativeReal, singleFloat, (IsA ArgOne positiveSingleFloat), TT)
           , (singleFloat, nonpositiveReal, (IsA ArgZero negativeSingleFloat), TT)
           , (negativeReal, singleFloat, TT, TT)
           , (nonpositiveReal, singleFloat, TT, TT)
           , (inexactReal, realZero, (IsA ArgZero negativeInexactReal), TT) -- <-type-pattern inexactreal
           , (realZero, inexactReal, (IsA ArgOne positiveInexactReal), TT)
           , (inexactReal, positiveReal, TT, TT)
           , (inexactReal, nonnegativeReal, TT, TT)
           , (nonnegativeReal, inexactReal, (IsA ArgOne positiveInexactReal), TT)
           , (inexactReal, nonpositiveReal, (IsA ArgZero negativeInexactReal), TT)
           , (negativeReal, inexactReal, TT, TT)
           , (nonpositiveReal, inexactReal, TT, TT)
           , (real, realZero, (IsA ArgZero negativeReal), TT) -- <-type-pattern real
           , (realZero, real, (IsA ArgOne positiveReal), TT)
           , (real, positiveReal, TT, TT)
           , (real, nonnegativeReal, TT, TT)
           , (nonnegativeReal, real, (IsA ArgOne positiveReal), TT)
           , (real, nonpositiveReal, (IsA ArgZero negativeReal), TT)
           , (negativeReal, real, TT, TT)
           , (nonpositiveReal, real, TT, TT) -- end of <-type-pattern
           , (real, real, TT, TT)]))
    
  , ("<=", (CompOp
             [ (integer, one, (IsA ArgZero (Or [nonpositiveInteger, one])), (IsA ArgZero positiveInteger))
             , (one, integer, (IsA ArgOne positiveInteger), (IsA ArgOne nonpositiveInteger))
             , (real, zero, (IsA ArgZero nonpositiveReal), (IsA ArgZero positiveReal))
             , (zero, real, (IsA ArgOne nonnegativeReal), (IsA ArgOne negativeReal))
             , (real, realZero, (IsA ArgZero nonpositiveReal), TT) -- False says nothing because of NaN
             , (realZero, real, (IsA ArgZero nonnegativeReal), TT) -- False says nothing because of NaN
             , (positiveByte, byte, (IsA ArgOne positiveByte), TT)
             , (byte, byte, TT, (IsA ArgZero positiveByte))
             , (positiveInteger, byte, (Conj (IsA ArgZero positiveByte) (IsA ArgOne positiveByte)), TT)
             , (positiveReal, byte, (IsA ArgOne positiveByte), TT)
             , (byte, positiveInteger, TT, (Conj (IsA ArgZero positiveByte) (IsA ArgOne positiveByte)))
             , (byte, positiveRational, TT, (IsA ArgZero positiveByte))
             , (nonnegativeInteger, byte, (IsA ArgZero byte), TT)
             , (byte, nonnegativeInteger, TT, (Conj (IsA ArgZero positiveByte) (IsA ArgOne byte)))
             , (byte, nonnegativeRational, TT, (IsA ArgZero positiveByte))
             , (positiveIndex, index, (IsA ArgOne positiveIndex), TT)
             , (index, index, TT, (IsA ArgZero positiveIndex))
             , (positiveInteger, index, (Conj (IsA ArgZero positiveIndex) (IsA ArgOne positiveIndex)), TT)
             , (positiveReal, index, (IsA ArgOne positiveIndex), TT)
             , (index, positiveInteger, TT, (Conj (IsA ArgZero positiveIndex) (IsA ArgOne positiveIndex)))
             , (index, positiveRational, TT, (IsA ArgZero positiveIndex))
             , (nonnegativeInteger, index, (IsA ArgZero index), TT)
             , (index, nonnegativeInteger, TT, (Conj (IsA ArgZero positiveIndex) (IsA ArgOne index)))
             , (index, nonnegativeRational, TT, (IsA ArgZero positiveIndex))
             , (positiveInteger, fixnum, (Conj (IsA ArgZero positiveFixnum) (IsA ArgOne positiveFixnum)), TT)
             , (positiveReal, fixnum, (IsA ArgOne positiveFixnum), TT)
             , (nonnegativeInteger, fixnum, (Conj (IsA ArgZero nonnegativeFixnum) (IsA ArgOne nonnegativeFixnum)), TT)
             , (nonnegativeReal, fixnum, (IsA ArgOne nonnegativeFixnum), TT)
             , (fixnum, nonnegativeInteger, TT, (Conj (IsA ArgZero positiveFixnum) (IsA ArgOne nonnegativeFixnum)))
             , (fixnum, nonnegativeRational, TT, (IsA ArgZero positiveFixnum))
             , (nonpositiveInteger, fixnum, TT, (Conj (IsA ArgZero nonpositiveFixnum) (IsA ArgOne negativeFixnum)))
             , (nonpositiveRational, fixnum, TT, (IsA ArgOne negativeFixnum))
             , (fixnum, negativeInteger, (Conj (IsA ArgZero negativeFixnum) (IsA ArgOne negativeFixnum)), TT)
             , (fixnum, negativeReal, (IsA ArgZero negativeFixnum), TT)
             , (fixnum, nonpositiveInteger, (Conj (IsA ArgZero nonpositiveFixnum) (IsA ArgOne nonpositiveFixnum)), TT)
             , (fixnum, nonpositiveReal, (IsA ArgZero nonpositiveFixnum), TT)
             , (real, positiveInfinity, (IsA ArgZero (Not inexactRealNaN)), (IsA ArgZero inexactRealNaN))
             , (negativeInfinity, real, (IsA ArgOne (Not inexactRealNaN)), (IsA ArgOne inexactRealNaN))
             , (positiveInfinity, real, (IsA ArgOne positiveInfinity), (IsA ArgOne (Not positiveInfinity)))
             , (real, negativeInfinity, (IsA ArgZero negativeInfinity), (IsA ArgZero (Not negativeInfinity)))
             , (integer, zero, (IsA ArgZero nonpositiveInteger), (IsA ArgZero positiveInteger)) -- <=-pat integer
             , (zero, integer, (IsA ArgOne nonnegativeInteger), (IsA ArgOne negativeInteger)) -- <=-pat integer
             , (integer, nonnegativeRealNoNaN, TT, (IsA ArgZero positiveInteger)) -- <=-pat integer
             , (positiveReal, integer, (IsA ArgOne positiveInteger), TT) -- <=-pat integer
             , (nonnegativeReal, integer, (IsA ArgOne nonnegativeInteger), TT) -- <=-pat integer
             , (nonpositiveRealNoNaN, integer, TT, (IsA ArgOne negativeInteger)) -- <=-pat integer
             , (integer, negativeReal, (IsA ArgZero negativeInteger), TT) -- <=-pat integer
             , (integer, nonpositiveReal, (IsA ArgZero nonpositiveInteger), TT) -- <=-pat integer
             , (rational, zero, (IsA ArgZero nonpositiveRational), (IsA ArgZero positiveRational)) -- <=-pat rational
             , (zero, rational, (IsA ArgOne nonnegativeRational), (IsA ArgOne negativeRational)) -- <=-pat rational
             , (rational, nonnegativeRealNoNaN, TT, (IsA ArgZero positiveRational)) -- <=-pat rational
             , (positiveReal, rational, (IsA ArgOne positiveRational), TT) -- <=-pat rational
             , (nonnegativeReal, rational, (IsA ArgOne nonnegativeRational), TT) -- <=-pat rational
             , (nonpositiveRealNoNaN, rational, TT, (IsA ArgOne negativeRational)) -- <=-pat rational
             , (rational, negativeReal, (IsA ArgZero negativeRational), TT) -- <=-pat rational
             , (rational, nonpositiveReal, (IsA ArgZero nonpositiveRational), TT) -- <=-pat rational
             , (float, realZeroNoNaN, (IsA ArgZero nonpositiveFloat), TT) -- <=-pat float
             , (realZeroNoNaN, float, (IsA ArgOne nonnegativeFloat), TT) -- <=-pat float
             , (float, nonnegativeRealNoNaN, TT, TT) -- <=-pat float
             , (positiveReal, float, (IsA ArgOne positiveFloat), TT) -- <=-pat float
             , (nonnegativeReal, float, (IsA ArgOne nonnegativeFloat), TT) -- <=-pat float
             , (nonpositiveRealNoNaN, float, TT, TT) -- <=-pat float
             , (float, negativeReal, (IsA ArgZero negativeFloat), TT) -- <=-pat float
             , (float, nonpositiveReal, (IsA ArgZero nonpositiveFloat), TT) -- <=-pat float
             , (singleFloat, realZeroNoNaN, (IsA ArgZero nonpositiveSingleFloat), TT) -- <=-pat singleFloat
             , (realZeroNoNaN, singleFloat, (IsA ArgOne nonnegativeSingleFloat), TT) -- <=-pat singleFloat
             , (singleFloat, nonnegativeRealNoNaN, TT, TT) -- <=-pat singleFloat
             , (positiveReal, singleFloat, (IsA ArgOne positiveSingleFloat), TT) -- <=-pat singleFloat
             , (nonnegativeReal, singleFloat, (IsA ArgOne nonnegativeSingleFloat), TT) -- <=-pat singleFloat
             , (nonpositiveRealNoNaN, singleFloat, TT, TT) -- <=-pat singleFloat
             , (singleFloat, negativeReal, (IsA ArgZero negativeSingleFloat), TT) -- <=-pat singleFloat
             , (singleFloat, nonpositiveReal, (IsA ArgZero nonpositiveSingleFloat), TT) -- <=-pat singleFloat
             , (inexactReal, realZeroNoNaN, (IsA ArgZero nonpositiveInexactReal), TT) -- <=-pat inexactReal
             , (realZeroNoNaN, inexactReal, (IsA ArgOne nonnegativeInexactReal), TT) -- <=-pat inexactReal
             , (inexactReal, nonnegativeRealNoNaN, TT, TT) -- <=-pat inexactReal
             , (positiveReal, inexactReal, (IsA ArgOne positiveInexactReal), TT) -- <=-pat inexactReal
             , (nonnegativeReal, inexactReal, (IsA ArgOne nonnegativeInexactReal), TT) -- <=-pat inexactReal
             , (nonpositiveRealNoNaN, inexactReal, TT, TT) -- <=-pat inexactReal
             , (inexactReal, negativeReal, (IsA ArgZero negativeInexactReal), TT) -- <=-pat inexactReal
             , (inexactReal, nonpositiveReal, (IsA ArgZero nonpositiveInexactReal), TT) -- <=-pat inexactReal
             , (real, realZeroNoNaN, (IsA ArgZero nonpositiveReal), TT) -- <=-pat real
             , (realZeroNoNaN, real, (IsA ArgOne nonnegativeReal), TT) -- <=-pat real
             , (real, nonnegativeRealNoNaN, TT, TT) -- <=-pat real
             , (positiveReal, real, (IsA ArgOne positiveReal), TT) -- <=-pat real
             , (nonnegativeReal, real, (IsA ArgOne nonnegativeReal), TT) -- <=-pat real
             , (nonpositiveRealNoNaN, real, TT, TT) -- <=-pat real
             , (real, negativeReal, (IsA ArgZero negativeReal), TT) -- <=-pat real
             , (real, nonpositiveReal, (IsA ArgZero nonpositiveReal), TT) -- <=-pat real
             , (real, real, TT, TT)]))
  ] -- end of opTypes

