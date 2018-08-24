module Types.SemanticOpTypes where

import Types.LazyBDD
import Types.NumericTower

opTypes :: [(String, OpSpec)]
opTypes =
  [ ("add1", (UnOp
              [ (zero, one)
              , (one, byte)
              , (byte, index)
              , (index, fixnum)
              , (integer, integer)
              , (rational, rational)
              , (float, float)
              , (singleFloat, singleFloat)
              , (floatComplex, floatComplex)
              , (singleFloatComplex, singleFloatComplex)
              , (nonpositiveFixnum, fixnum)
              , (negativeInteger, nonpositiveInteger)
              , (nonnegativeReal, positiveReal)
              , (number, number)]))
  , ("sub1", (UnOp
              [ (one, zero)
              , (positiveByte, byte)
              , (positiveIndex, index)
              , (nonnegativeFixnum, fixnum)
              , (positiveInteger, nonnegativeInteger)
              , (integer, integer)
              , (rational, rational)
              , (float, float)
              , (singleFloat, singleFloat)
              , (nonpositiveReal, negativeReal)
              , (floatComplex, floatComplex)
              , (singleFloatComplex, singleFloatComplex)
              , (number, number)]))
  , ("abs", (UnOp
             [ (realZero, realZero)
             , (integer, nonnegativeInteger)
             , (rational, nonnegativeRational)
             , (float, nonnegativeFloat)
             , (singleFloat, nonnegativeSingleFloat)
             , ((tyOr' [positiveReal, negativeReal]), positiveReal)]))
    
  , ("+", (BinOp
            [ (byte, byte, index)
            , (index, index, nonnegativeFixnum)
            , (negativeFixnum, one, nonpositiveFixnum)
            , (one, negativeFixnum, nonpositiveFixnum)
            , (nonpositiveFixnum, nonnegativeFixnum, fixnum)
            , (nonnegativeFixnum, nonpositiveFixnum, fixnum)
            , (integer, integer, integer)
            , (float, real, float)
            , (real, float, float)
            , (singleFloat, (tyOr' [rational, singleFloat]), singleFloat)
            , ((tyOr' [rational, singleFloat]), singleFloat, singleFloat)
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
            , (singleFloatComplex, (tyOr' [rational, singleFloat, singleFloatComplex]), singleFloatComplex)
            , ((tyOr' [rational, singleFloat, singleFloatComplex]), singleFloatComplex, singleFloatComplex)
            , (number, number, number)])) 
    
  , ("-", (BinOp
            [ (zero, positiveReal, negativeReal) -- negation pattern
            , (zero, nonnegativeReal, nonpositiveReal) -- negation pattern
            , (zero, negativeReal, positiveReal) -- negation pattern
            , (zero, nonpositiveReal, nonnegativeReal) -- negation pattern
            , (one, one, zero)
            , (positiveByte, one, byte)
            , (positiveIndex, one, index)
            , (positiveInteger, one, nonnegativeInteger)
            , (nonnegativeFixnum, nonnegativeFixnum, fixnum)
            , (negativeFixnum, nonpositiveFixnum, fixnum)
            , (integer, integer, integer)
            , (positiveRational, nonpositiveRational, positiveRational)
            , (negativeRational, nonnegativeRational, negativeRational)
            , (float, real, float)
            , (real, float, float)
            , (singleFloat, (tyOr' [singleFloat, rational]), singleFloat)
            , ((tyOr' [singleFloat, rational]), singleFloat, singleFloat)
            , (real, real, real)
            , (exactNumber, exactNumber, exactNumber)
            , (floatComplex, number, floatComplex)
            , (number, floatComplex, floatComplex)
            , (singleFloatComplex, (tyOr' [singleFloatComplex, exactNumber]), singleFloatComplex)
            , ((tyOr' [singleFloatComplex, exactNumber]), singleFloatComplex, singleFloatComplex)
            , (number, number, number)]))

  , ("*", (BinOp
            [ (zero, number, zero)
            , (number, zero, zero)
            , (byte, byte, index)
            , (integer, integer, integer)
            , (tyAnd' [rational, (tyNot zero)], tyAnd' [rational, (tyNot zero)], tyAnd' [rational, (tyNot zero)])
            , (float, (tyOr' [positiveReal, negativeReal]), float)
            , ((tyOr' [positiveReal, negativeReal]), float, float)
            , (float, float, float)
            , (singleFloat, (tyOr' [positiveRational, negativeRational, singleFloat]), singleFloat)
            , ((tyOr' [positiveRational, negativeRational, singleFloat]), singleFloat, singleFloat)
            , (inexactReal, inexactReal, inexactReal)
            , (nonnegativeReal, nonnegativeReal, nonnegativeReal) -- (* +inf.0 0.0) -> +nan.0
            , (nonpositiveReal, nonpositiveReal, nonnegativeReal)
            , (nonpositiveReal, nonnegativeReal, nonpositiveReal)
            , (nonnegativeReal, nonpositiveReal, nonpositiveReal)
            , (floatComplex, (tyOr' [inexactComplex, inexactReal, positiveRational, negativeRational]), floatComplex)
            , ((tyOr' [inexactComplex, inexactReal, positiveRational, negativeRational]), floatComplex, floatComplex)
            , (singleFloatComplex, (tyOr' [singleFloatComplex, singleFloat, positiveRational, negativeRational]), singleFloatComplex)
            , ((tyOr' [singleFloatComplex, singleFloat, positiveRational, negativeRational]), singleFloatComplex, singleFloatComplex)
            , (inexactComplex, (tyOr' [inexactComplex, inexactReal, positiveRational, negativeRational]), inexactComplex)
            , ((tyOr' [inexactComplex, inexactReal, positiveRational, negativeRational]), inexactComplex, inexactComplex)
            , (number, number, number)]))

  , ("/", (BinOp
            [ (number, zero, emptyTy)
            , (zero, number, zero)
            , (one, one, one)
            , (tyAnd' [rational, (tyNot zero)], tyAnd' [rational, (tyNot zero)], tyAnd' [rational, (tyNot zero)])
            , ((tyOr' [positiveReal, negativeReal, float]), float, float)
            , (float, real, float) -- if any argument after the first is exact 0, not a problem
            , (singleFloat, (tyOr' [positiveRational, negativeRational, singleFloat]), singleFloat)
            , ((tyOr' [positiveRational, negativeRational, singleFloat]), singleFloat, singleFloat)
            , (inexactReal, inexactReal, inexactReal)
            , (positiveReal, positiveReal, nonnegativeReal)
            , (negativeReal, negativeReal, nonnegativeReal) -- 0.0 is non-neg, but doesn't preserve sign
            , (negativeReal, positiveReal, nonpositiveReal) -- idem
            , (positiveReal, negativeReal, nonpositiveReal) -- idem
            , ((tyOr' [inexactComplex, inexactReal, positiveRational, negativeRational]), floatComplex, floatComplex)
            , (floatComplex, number, floatComplex) -- if any argument after the first is exact 0, not a problem
            , (singleFloatComplex, (tyOr' [singleFloatComplex, singleFloat, positiveRational, negativeRational]), singleFloatComplex)
            , ((tyOr' [singleFloatComplex, singleFloat, positiveRational, negativeRational]), singleFloatComplex, singleFloatComplex)
            , (inexactComplex, (tyOr' [inexactComplex, inexactReal, positiveRational, negativeRational]), inexactComplex)
            , ((tyOr' [inexactComplex, inexactReal, positiveRational, negativeRational]), inexactComplex, inexactComplex)
            , (number, number, number)]))

  , ("max", (BinOp
              [ (one, one, one)
              , (one, zero, one)
              , (zero, one, one)
              , (positiveByte, byte, positiveByte)
              , (byte, positiveByte, positiveByte)
              , (index, index, index)
              , (fixnum, fixnum, fixnum)
              , (integer, integer, integer)
              , (rational, rational, rational)
              , (float, float, float)
              , (singleFloat, singleFloat, singleFloat)
              , (inexactRealPositiveZero, inexactRealPositiveZero, inexactRealPositiveZero)
              , (inexactRealNegativeZero, inexactRealNegativeZero, inexactRealNegativeZero)
              , (inexactReal, inexactReal, inexactReal)
              , (positiveReal, real, positiveReal)
              , (real, positiveReal, positiveReal)
              , (nonnegativeReal, real, nonnegativeReal)
              , (real, nonnegativeReal, nonnegativeReal)
              , (negativeReal, negativeReal, negativeReal)
              , (nonpositiveReal, nonpositiveReal, nonpositiveReal)]))

  , ("min", (BinOp
              [ (one, one, one)
              , (index, index, index)
              , (byte, nonnegativeInteger, byte)
              , (nonnegativeInteger, byte, byte)
              , (nonnegativeFixnum, nonnegativeInteger, nonnegativeFixnum)
              , (nonnegativeInteger, nonnegativeFixnum, nonnegativeFixnum)
              , (fixnum, fixnum, fixnum)
              , (integer, integer, integer)
              , (rational, rational, rational)
              , (float, float, float)
              , (singleFloat, singleFloat, singleFloat)
              , (inexactRealPositiveZero, inexactRealPositiveZero, inexactRealPositiveZero)
              , (inexactRealNegativeZero, inexactRealNegativeZero, inexactRealNegativeZero)
              , (inexactReal, inexactReal, inexactReal)
              , (positiveReal, positiveReal, positiveReal)
              , (nonnegativeReal, nonnegativeReal, nonnegativeReal)
              , (negativeReal, real, negativeReal)
              , (real, negativeReal, negativeReal)
              , (nonpositiveReal, real, nonpositiveReal)
              , (real, nonpositiveReal, nonpositiveReal)]))

    
  , ("<", (BinOp
           [ -- general cases --
             -- -- -- -- -- -- -- -- --
             (realNoNaN, realNoNaN, bool)
           , (someNaN, real, false)
           , (real, someNaN, false)
             -- positive/nonpositive cases --
           , (nonpositiveRealNoNaN, positiveRealNoNaN, true)
           , (positiveReal, nonpositiveReal, false)
             -- zero/negative cases --
           , (negativeRealNoNaN, realZeroNoNaN, true)
           , (realZero, negativeReal, false)
           -- bounded type cases --
           , (negativeInfinity, tyAnd' [realNoNaN, (tyNot negativeInfinity)], true)
           , (real, negativeInfinity, false)
           , (negativeIntegerNotFixnum, tyAnd' [integer, (tyNot negativeIntegerNotFixnum)], true)
           , (tyAnd' [integer, (tyNot negativeIntegerNotFixnum)], negativeIntegerNotFixnum, false)
           , (realZero, realZero, false)
           , (one, one, false)
           , (one, tyAnd' [positiveInteger, (tyNot one)], true)
           , (tyAnd' [positiveInteger, (tyNot one)], one, false)
           , (byte, positiveIntegerNotByte, true)
           , (positiveIntegerNotByte, byte, false)
           , (index, positiveIntegerNotIndex, true)
           , (positiveIntegerNotIndex, index, false)
           , (fixnum, positiveIntegerNotFixnum, true)
           , (positiveIntegerNotFixnum, fixnum, false)
           , (tyAnd' [realNoNaN, (tyNot positiveInfinity)], positiveInfinity, true)
           , (positiveInfinity, real, false)]))
    
  , ("<=", (BinOp
           [ -- general cases --
             -- -- -- -- -- -- -- -- --
             (realNoNaN, realNoNaN, bool)
           , (someNaN, real, false)
           , (real, someNaN, false)
             -- negative cases --
           , (negativeRealNoNaN, nonnegativeRealNoNaN, true)
           , (nonnegativeRealNoNaN, negativeRealNoNaN, false)
           -- zero cases
           , (realZero, realZero, true)
             -- positive cases --
           , (nonpositiveRealNoNaN, positiveRealNoNaN, true)
           , (positiveRealNoNaN, nonpositiveRealNoNaN, false)
           -- bounded type cases --
           , (negativeInfinity, realNoNaN, true)
           , (tyAnd' [realNoNaN, (tyNot negativeInfinity)], negativeInfinity, false)
           , (negativeIntegerNotFixnum, tyAnd' [integer, (tyNot negativeIntegerNotFixnum)], true)
           , (tyAnd' [integer, (tyNot negativeIntegerNotFixnum)], negativeIntegerNotFixnum, false)
           , (one, positiveInteger, true)
           , (tyAnd'[positiveInteger, (tyNot one)], one, false)
           , (byte, positiveIntegerNotByte, true)
           , (positiveIntegerNotByte, byte, false)
           , (index, positiveIntegerNotIndex, true)
           , (positiveIntegerNotIndex, index, false)
           , (fixnum, positiveIntegerNotFixnum, true)
           , (positiveIntegerNotFixnum, fixnum, false)
           , (realNoNaN, positiveInfinity, true)
           , (positiveInfinity, tyAnd' [realNoNaN, (tyNot positiveInfinity)], false)]))

  , ("=", (BinOp
            [ (someNaN, number, false)
            , (number, someNaN, false)
            , (realZero, realZero, true)
            , (tyAnd'[exactNumber, (tyNot realZero)], realZero, false)
            , (realZero, tyAnd'[exactNumber, (tyNot realZero)], false)
            , (tyAnd'[exactNumber, (tyNot one)], one, false)
            , (one, tyAnd'[exactNumber, (tyNot one)], false)
            , (tyAnd'[exactNumber, (tyNot byte)], byte, false)
            , (byte, tyAnd'[exactNumber, (tyNot byte)], false)
            , (tyAnd'[exactNumber, (tyNot index)], index, false)
            , (index, tyAnd'[exactNumber, (tyNot index)], false)
            , (tyAnd'[exactNumber, (tyNot fixnum)], fixnum, false)
            , (fixnum, tyAnd'[exactNumber, (tyNot fixnum)], false)
            , (tyAnd'[exactNumber, (tyNot integer)], integer, false)
            , (integer, tyAnd'[exactNumber, (tyNot integer)], false)
            , (tyAnd'[exactNumber, (tyNot rational)], rational, false)
            , (rational, tyAnd'[exactNumber, (tyNot rational)], false)
            , (nonpositiveReal, positiveReal, false)
            , (positiveReal, nonpositiveReal, false)
            , (nonnegativeReal, negativeReal, false)
            , (negativeReal, nonnegativeReal, false)
            , (number, number, bool)]))
  ]

