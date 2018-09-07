module Types.SemanticOpTypes where

import Types.LazyBDD
import Types.BaseEnv

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

  , ("sqr", (UnOp [ (zero, zero)
                  , (one, one)
                  , (byte, index)
                  , (integer, nonnegativeInteger)
                  , (positiveRational, positiveRational)
                  , (rational, nonnegativeRational)
                  , (float, nonnegativeFloat)
                  , (singleFloat, nonnegativeSingleFloat)
                  , (floatComplex, floatComplex)
                  , (singleFloatComplex, singleFloatComplex)
                  , (exactNumber, exactNumber)
                  , (number, number)]))
    
  , ("sqrt", (UnOp [ (zero, zero)
                   , (one, one)
                   , (nonnegativeFloat, nonnegativeFloat)
                   , (nonnegativeSingleFloat, nonnegativeSingleFloat)
                   , (inexactRealPositiveZero, inexactRealPositiveZero)
                   , (inexactRealNegativeZero, inexactRealNegativeZero)
                   , (realZero, realZero)
                   , (positiveReal, positiveReal)
                   , (floatComplex, floatComplex)
                   , (singleFloatComplex, singleFloatComplex)
                   , (number, number)]))
    
  , ("expt", (BinOp [ (one, rational, one)
                    , (number, zero, one) -- will error if negative
                    , (integer, nonnegativeInteger, integer)
                    , (positiveRational, integer, positiveRational)
                    , (nonnegativeRational, integer, nonnegativeRational)
                    , (rational, integer, rational)
                    , (nonnegativeFloat, real, (tyOr nonnegativeFloat one))
                    , (positiveReal, nonnegativeFloat, (tyOr nonnegativeFloat one))
                    , (float, (tyOr negativeFixnum positiveFixnum), float)
                    , (float, float, (tyOr float floatComplex))
                    , (singleFloat, (tyOr negativeFixnum positiveFixnum), singleFloat)
                    , (singleFloat, singleFloat, (tyOr singleFloat singleFloatComplex))
                    , (positiveReal, real, nonnegativeReal)
                    , (nonnegativeReal, real, real)
                    , (inexactReal, inexactReal, (tyOr inexactReal inexactComplex))
                    , (real, nonnegativeInteger, real)
                    , (floatComplex, float, (tyOr floatComplex float))
                    , (floatComplex, inexactReal, (tyOr floatComplex inexactReal))
                    , (floatComplex, inexactComplex, floatComplex)
                    , (singleFloatComplex, singleFloatComplex, singleFloatComplex)
                    , (singleFloatComplex, singleFloat, (tyOr singleFloatComplex singleFloat))
                    , (inexactComplex, inexactComplex, inexactComplex)
                    , (number, number, number)]))
    
  , ("modulo", (BinOp [])) -- TODO
  , ("quotient", (BinOp [])) -- TODO
    
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
             (realNoNaN, realNoNaN, boolTy)
           , (someNaN, real, falseTy)
           , (real, someNaN, falseTy)
             -- positive/nonpositive cases --
           , (nonpositiveRealNoNaN, positiveRealNoNaN, trueTy)
           , (positiveReal, nonpositiveReal, falseTy)
             -- zero/negative cases --
           , (negativeRealNoNaN, realZeroNoNaN, trueTy)
           , (realZero, negativeReal, falseTy)
           -- bounded type cases --
           , (negativeInfinity, tyAnd' [realNoNaN, (tyNot negativeInfinity)], trueTy)
           , (real, negativeInfinity, falseTy)
           , (negativeIntegerNotFixnum, tyAnd' [integer, (tyNot negativeIntegerNotFixnum)], trueTy)
           , (tyAnd' [integer, (tyNot negativeIntegerNotFixnum)], negativeIntegerNotFixnum, falseTy)
           , (realZero, realZero, falseTy)
           , (one, one, falseTy)
           , (one, tyAnd' [positiveInteger, (tyNot one)], trueTy)
           , (tyAnd' [positiveInteger, (tyNot one)], one, falseTy)
           , (byte, positiveIntegerNotByte, trueTy)
           , (positiveIntegerNotByte, byte, falseTy)
           , (index, positiveIntegerNotIndex, trueTy)
           , (positiveIntegerNotIndex, index, falseTy)
           , (fixnum, positiveIntegerNotFixnum, trueTy)
           , (positiveIntegerNotFixnum, fixnum, falseTy)
           , (tyAnd' [realNoNaN, (tyNot positiveInfinity)], positiveInfinity, trueTy)
           , (positiveInfinity, real, falseTy)]))
    
  , ("<=", (BinOp
           [ -- general cases --
             -- -- -- -- -- -- -- -- --
             (realNoNaN, realNoNaN, boolTy)
           , (someNaN, real, falseTy)
           , (real, someNaN, falseTy)
             -- negative cases --
           , (negativeRealNoNaN, nonnegativeRealNoNaN, trueTy)
           , (nonnegativeRealNoNaN, negativeRealNoNaN, falseTy)
           -- zero cases
           , (realZeroNoNaN, realZeroNoNaN, trueTy)
             -- positive cases --
           , (nonpositiveRealNoNaN, positiveRealNoNaN, trueTy)
           , (positiveRealNoNaN, nonpositiveRealNoNaN, falseTy)
           -- bounded type cases --
           , (negativeInfinity, realNoNaN, trueTy)
           , (tyAnd' [realNoNaN, (tyNot negativeInfinity)], negativeInfinity, falseTy)
           , (negativeIntegerNotFixnum, tyAnd' [integer, (tyNot negativeIntegerNotFixnum)], trueTy)
           , (tyAnd' [integer, (tyNot negativeIntegerNotFixnum)], negativeIntegerNotFixnum, falseTy)
           , (one, positiveInteger, trueTy)
           , (tyAnd' [positiveInteger, (tyNot one)], one, falseTy)
           , (byte, positiveIntegerNotByte, trueTy)
           , (positiveIntegerNotByte, byte, falseTy)
           , (index, positiveIntegerNotIndex, trueTy)
           , (positiveIntegerNotIndex, index, falseTy)
           , (fixnum, positiveIntegerNotFixnum, trueTy)
           , (positiveIntegerNotFixnum, fixnum, falseTy)
           , (realNoNaN, positiveInfinity, trueTy)
           , (positiveInfinity, tyAnd' [realNoNaN, (tyNot positiveInfinity)], falseTy)]))

  , ("=", (BinOp
            [ (someNaN, number, falseTy)
            , (number, someNaN, falseTy)
            , (realZeroNoNaN, realZeroNoNaN, trueTy)
            , (tyAnd' [number, (tyNot realZeroNoNaN)], realZeroNoNaN, falseTy)
            , (realZeroNoNaN, tyAnd' [number, (tyNot realZeroNoNaN)], falseTy)
            , (tyAnd' [exactNumber, (tyNot one)], one, falseTy)
            , (one, tyAnd' [exactNumber, (tyNot one)], falseTy)
            , (tyAnd' [exactNumber, (tyNot byte)], byte, falseTy)
            , (byte, tyAnd' [exactNumber, (tyNot byte)], falseTy)
            , (tyAnd' [exactNumber, (tyNot index)], index, falseTy)
            , (index, tyAnd' [exactNumber, (tyNot index)], falseTy)
            , (tyAnd' [exactNumber, (tyNot fixnum)], fixnum, falseTy)
            , (fixnum, tyAnd' [exactNumber, (tyNot fixnum)], falseTy)
            , (tyAnd' [exactNumber, (tyNot integer)], integer, falseTy)
            , (integer, tyAnd' [exactNumber, (tyNot integer)], falseTy)
            , (tyAnd' [exactNumber, (tyNot rational)], rational, falseTy)
            , (rational, tyAnd' [exactNumber, (tyNot rational)], falseTy)
            , (nonpositiveReal, positiveReal, falseTy)
            , (positiveReal, nonpositiveReal, falseTy)
            , (nonnegativeReal, negativeReal, falseTy)
            , (negativeReal, nonnegativeReal, falseTy)
            , (number, number, boolTy)]))
  ]

