module Types.SemanticOpTypes where

import Types.Syntax

import Types.Syntax

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
             , ((Or [positiveReal, negativeReal]), positiveReal)]))
    
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
            , (singleFloat, (Or [rational, singleFloat]), singleFloat)
            , ((Or [rational, singleFloat]), singleFloat, singleFloat)
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
            , (singleFloat, (Or [singleFloat, rational]), singleFloat)
            , ((Or [singleFloat, rational]), singleFloat, singleFloat)
            , (real, real, real)
            , (exactNumber, exactNumber, exactNumber)
            , (floatComplex, number, floatComplex)
            , (number, floatComplex, floatComplex)
            , (singleFloatComplex, (Or [singleFloatComplex, exactNumber]), singleFloatComplex)
            , ((Or [singleFloatComplex, exactNumber]), singleFloatComplex, singleFloatComplex)
            , (number, number, number)]))

  , ("*", (BinOp
            [ (zero, number, zero)
            , (number, zero, zero)
            , (byte, byte, index)
            , (integer, integer, integer)
            , (positiveRational, positiveRational, positiveRational)
            , (negativeRational, negativeRational, positiveRational)
            , (negativeRational, positiveRational, negativeRational)
            , (positiveRational, negativeRational, negativeRational)
            , (float, (Or [positiveReal, negativeReal]), float)
            , ((Or [positiveReal, negativeReal]), float, float)
            , (float, float, float)
            , (singleFloat, (Or [positiveRational, negativeRational, singleFloat]), singleFloat)
            , ((Or [positiveRational, negativeRational, singleFloat]), singleFloat, singleFloat)
            , (inexactReal, inexactReal, inexactReal)
            , (nonnegativeReal, nonnegativeReal, nonnegativeReal) -- (* +inf.0 0.0) -> +nan.0
            , (nonpositiveReal, nonpositiveReal, nonnegativeReal)
            , (nonpositiveReal, nonnegativeReal, nonpositiveReal)
            , (nonnegativeReal, nonpositiveReal, nonpositiveReal)
            --, (real, real, real)
            , (floatComplex, (Or [inexactComplex, inexactReal, positiveRational, negativeRational]), floatComplex)
            , ((Or [inexactComplex, inexactReal, positiveRational, negativeRational]), floatComplex, floatComplex)
            , (singleFloatComplex, (Or [singleFloatComplex, singleFloat, positiveRational, negativeRational]), singleFloatComplex)
            , ((Or [singleFloatComplex, singleFloat, positiveRational, negativeRational]), singleFloatComplex, singleFloatComplex)
            , (inexactComplex, (Or [inexactComplex, inexactReal, positiveRational, negativeRational]), inexactComplex)
            , ((Or [inexactComplex, inexactReal, positiveRational, negativeRational]), inexactComplex, inexactComplex)
            , (number, number, number)]))

  , ("/", (BinOp
            [ (zero, number, zero)
            , (one, one, one)
            , (positiveRational, positiveRational, positiveRational)
            , (nonnegativeRational, nonnegativeRational, nonnegativeRational)
            , (negativeRational, negativeRational, positiveRational)
            , (negativeRational, positiveRational, negativeRational)
            , (positiveRational, negativeRational, negativeRational)
            , (nonpositiveRational, nonpositiveRational, nonnegativeRational)
            , (nonpositiveRational, nonnegativeRational, nonpositiveRational)
            , (nonnegativeRational, nonpositiveRational, nonpositiveRational)
            , ((Or [positiveReal, negativeReal, float]), float, float)
            , (float, real, float) -- if any argument after the first is exact 0, not a problem
            , (singleFloat, (Or [positiveRational, negativeRational, singleFloat]), singleFloat)
            , ((Or [positiveRational, negativeRational, singleFloat]), singleFloat, singleFloat)
            , (inexactReal, inexactReal, inexactReal)
            , (positiveReal, positiveReal, nonnegativeReal)
            , (negativeReal, negativeReal, nonnegativeReal) -- 0.0 is non-neg, but doesn't preserve sign
            , (negativeReal, positiveReal, nonpositiveReal) -- idem
            , (positiveReal, negativeReal, nonpositiveReal) -- idem
            , (real, real, real)
            , ((Or [inexactComplex, inexactReal, positiveRational, negativeRational]), floatComplex, floatComplex)
            , (floatComplex, number, floatComplex) -- if any argument after the first is exact 0, not a problem
            , (singleFloatComplex, (Or [singleFloatComplex, singleFloat, positiveRational, negativeRational]), singleFloatComplex)
            , ((Or [singleFloatComplex, singleFloat, positiveRational, negativeRational]), singleFloatComplex, singleFloatComplex)
            , (inexactComplex, (Or [inexactComplex, inexactReal, positiveRational, negativeRational]), inexactComplex)
            , ((Or [inexactComplex, inexactReal, positiveRational, negativeRational]), inexactComplex, inexactComplex)
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
           , (someNaN, real, F)
           , (real, someNaN, F)
             -- positive/nonpositive cases --
           , (nonpositiveRealNoNaN, positiveRealNoNaN, T)
           , (positiveReal, nonpositiveReal, F)
             -- zero/negative cases --
           , (negativeRealNoNaN, realZeroNoNaN, T)
           , (realZero, negativeReal, F)
           -- bounded type cases --
           , (negativeInfinity, And [realNoNaN, (Not negativeInfinity)], T)
           , (real, negativeInfinity, F)
           , (negativeIntegerNotFixnum, And [integer, (Not negativeIntegerNotFixnum)], T)
           , (And [integer, (Not negativeIntegerNotFixnum)], negativeIntegerNotFixnum, F)
           , (realZero, realZero, F)
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
           , (positiveInfinity, real, F)]))
    
  , ("<=", (CompOp
             [ (integer, one, (IsA ArgZero (Or [nonpositiveInteger, one])), (IsA ArgZero positiveInteger))
             , (one, integer, (IsA ArgOne positiveInteger), (IsA ArgOne nonpositiveInteger))
             , (real, zero, (IsA ArgZero nonpositiveReal), (IsA ArgZero positiveReal))
             , (zero, real, (IsA ArgOne nonnegativeReal), (IsA ArgOne negativeReal))
             , (nonnegativeInteger, byte, (IsA ArgZero byte), TT)
             , (byte, nonnegativeInteger, TT, (Conj (IsA ArgZero positiveByte) (IsA ArgOne byte)))
             , (nonnegativeInteger, index, (IsA ArgZero index), TT)
             , (index, nonnegativeInteger, TT, (Conj (IsA ArgZero positiveIndex) (IsA ArgOne index)))
             , (nonnegativeInteger, fixnum, (Conj (IsA ArgZero nonnegativeFixnum) (IsA ArgOne nonnegativeFixnum)), TT)
             , (fixnum, nonnegativeInteger, TT, (Conj (IsA ArgZero positiveFixnum) (IsA ArgOne nonnegativeFixnum)))
             , (nonpositiveInteger, fixnum, TT, (Conj (IsA ArgZero nonpositiveFixnum) (IsA ArgOne negativeFixnum)))
             , (fixnum, nonpositiveInteger, (Conj (IsA ArgZero nonpositiveFixnum) (IsA ArgOne nonpositiveFixnum)), TT)
             , (real, positiveInfinity, (IsA ArgZero (Not inexactRealNaN)), (IsA ArgZero inexactRealNaN))
             , (negativeInfinity, real, (IsA ArgOne (Not inexactRealNaN)), (IsA ArgOne inexactRealNaN))
             , (positiveInfinity, real, (IsA ArgOne positiveInfinity), (IsA ArgOne (Not positiveInfinity)))
             , (real, negativeInfinity, (IsA ArgZero negativeInfinity), (IsA ArgZero (Not negativeInfinity)))
             , (rational, nonnegativeRealNoNaN, TT, (IsA ArgZero positiveRational)) -- <=-pat rational
             , (nonpositiveRealNoNaN, rational, TT, (IsA ArgOne negativeRational)) -- <=-pat rational
             , (positiveReal, real, (IsA ArgOne positiveReal), TT) -- <=-pat real
             , (nonnegativeReal, real, (IsA ArgOne nonnegativeReal), TT) -- <=-pat real
             , (real, negativeReal, (IsA ArgZero negativeReal), TT) -- <=-pat real
             , (real, nonpositiveReal, (IsA ArgZero nonpositiveReal), TT) -- <=-pat real
             , (real, real, TT, TT)]))]

