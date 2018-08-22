module Types.SyntacticOpTypesPlus where

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
              , (real, real)
              , (inexactReal, inexactReal)
              , (inexactComplex, inexactComplex)
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
              , (inexactReal, inexactReal)
              , (nonpositiveReal, negativeReal)
              , (real, real)
              , (floatComplex, floatComplex)
              , (singleFloatComplex, singleFloatComplex)
              , (inexactComplex, inexactComplex)
              , (number, number)]))
  , ("abs", (UnOp
             [ (realZero, realZero)
             , (integer, nonnegativeInteger)
             , (rational, nonnegativeRational)
             , (float, nonnegativeFloat)
             , (singleFloat, nonnegativeSingleFloat)
             , (inexactReal, nonnegativeInexactReal)
             , ((Or [positiveReal, negativeReal]), positiveReal)
             , (real, nonnegativeReal)]))
    
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
            , (nonnegativeRational, nonpositiveRational, nonnegativeRational)
            , (negativeRational, nonnegativeRational, negativeRational)
            , (nonpositiveRational, nonnegativeRational, nonpositiveRational)
            , (float, real, float)
            , (real, float, float)
            , (singleFloat, (Or [singleFloat, rational]), singleFloat)
            , ((Or [singleFloat, rational]), singleFloat, singleFloat)
            , (inexactReal, (Or [inexactReal, rational]), inexactReal)
            , ((Or [inexactReal, rational]), inexactReal, inexactReal)
            , (real, real, real)
            , (exactNumber, exactNumber, exactNumber)
            , (floatComplex, number, floatComplex)
            , (number, floatComplex, floatComplex)
            , (singleFloatComplex, (Or [singleFloatComplex, exactNumber]), singleFloatComplex)
            , ((Or [singleFloatComplex, exactNumber]), singleFloatComplex, singleFloatComplex)
            , (inexactComplex, (Or [inexactComplex, exactNumber]), inexactComplex)
            , ((Or [inexactComplex, exactNumber]), inexactComplex, inexactComplex)
            , (number, number, number)]))

  , ("*", (BinOp
            [ (zero, number, zero)
            , (number, zero, zero)
            , (byte, byte, index)
            , (integer, integer, integer)
            , (And [rational, (Not zero)], And [rational, (Not zero)], And [rational, (Not zero)])
            , (rational, rational, rational)
            , (float, (Or [positiveReal, negativeReal]), float)
            , ((Or [positiveReal, negativeReal]), float, float)
            , (float, float, float)
            , (singleFloat, (Or [positiveRational, negativeRational, singleFloat]), singleFloat)
            , ((Or [positiveRational, negativeRational, singleFloat]), singleFloat, singleFloat)
            , (inexactReal, (Or [positiveRational, negativeRational, inexactReal]), inexactReal)
            , ((Or [positiveRational, negativeRational, inexactReal]), inexactReal, inexactReal)
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
            , (nonnegativeRational, nonnegativeRational, nonnegativeRational)
            , (nonpositiveRational, nonpositiveRational, nonnegativeRational)
            , (nonpositiveRational, nonnegativeRational, nonpositiveRational)
            , (nonnegativeRational, nonpositiveRational, nonpositiveRational)
            , (And [rational, (Not zero)], And [rational, (Not zero)], And [rational, (Not zero)])
            , (rational, rational, rational)
            , ((Or [positiveReal, negativeReal, float]), float, float)
            , (float, real, float) -- if any argument after the first is exact 0, not a problem
            , (singleFloat, (Or [positiveRational, negativeRational, singleFloat]), singleFloat)
            , ((Or [positiveRational, negativeRational, singleFloat]), singleFloat, singleFloat)
            , (inexactReal, (Or [positiveRational, negativeRational, inexactReal]), inexactReal)
            , ((Or [positiveRational, negativeRational, inexactReal]), inexactReal, inexactReal)
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
              , (nonpositiveReal, nonpositiveReal, nonpositiveReal)
              , (real, real, real)]))

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
              , (real, nonpositiveReal, nonpositiveReal)
              , (real, real, real)]))

    
  , ("<", (CompOp
           [ (integer, one, (IsA ArgZero nonpositiveInteger), (IsA ArgZero positiveInteger))
           , (real, zero, (IsA ArgZero negativeReal), (IsA ArgZero nonnegativeReal))
           , (zero, real, (IsA ArgOne positiveReal), (IsA ArgOne nonpositiveReal))
           , (nonnegativeInteger, byte, (Conj (IsA ArgZero byte) (IsA ArgOne positiveByte)), TT)
           , (byte, nonnegativeInteger, TT, (IsA ArgOne byte))
           , (nonnegativeInteger, index, (Conj (IsA ArgZero index) (IsA ArgOne positiveIndex)), TT)
           , (index, nonnegativeInteger, TT, (IsA ArgOne index))
           , (fixnum, nonnegativeInteger, TT, (Conj (IsA ArgZero nonnegativeFixnum) (IsA ArgOne nonnegativeFixnum)))
           , (nonnegativeInteger, fixnum, (Conj (IsA ArgZero nonnegativeFixnum) (IsA ArgOne positiveFixnum)), TT)
           , (fixnum, nonpositiveInteger, (Conj (IsA ArgZero negativeFixnum) (IsA ArgOne nonpositiveFixnum)), TT)
           , (nonpositiveInteger, fixnum, TT, (Conj (IsA ArgZero nonpositiveFixnum) (IsA ArgOne nonpositiveFixnum)))
           , (real, positiveInfinity, (IsA ArgZero (Not (Or [inexactRealNaN, positiveInfinity]))), (IsA ArgZero (Or [inexactRealNaN, positiveInfinity])))
           , (negativeInfinity, real, (IsA ArgOne (Not (Or [inexactRealNaN, negativeInfinity]))), (IsA ArgOne (Or [inexactRealNaN, negativeInfinity])))
           , (positiveInfinity, real, FF, TT)
           , (real, negativeInfinity, FF, TT)
           , (rational, positiveRealNoNaN, TT, (IsA ArgZero positiveRational)) -- AMK added NoNaN
           , (rational, nonnegativeRealNoNaN, TT, (IsA ArgZero nonnegativeRational)) -- AMK added NoNaN
           , (negativeRealNoNaN, rational, TT, (IsA ArgOne negativeRational)) -- AMK added NoNaN
           , (nonpositiveRealNoNaN, rational, TT, (IsA ArgOne nonpositiveRational)) -- AMK added NoNaN
           , (nonnegativeReal, real, (IsA ArgOne positiveReal), TT)
           , (real, nonpositiveReal, (IsA ArgZero negativeReal), TT)
           , (real, real, TT, TT)]))
    
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
             , (real, real, TT, TT)]))

  , ("=", (CompOp
            [ (real, realZero, (IsA ArgZero realZeroNoNaN), (IsA ArgZero (Not realZeroNoNaN)))
            , (realZero, real, (IsA ArgOne realZeroNoNaN), (IsA ArgOne (Not realZeroNoNaN)))
            , (exactNumber, one, (IsA ArgZero one), (IsA ArgZero (Not one)))
            , (one, exactNumber, (IsA ArgOne one), (IsA ArgOne (Not one)))
            , (exactNumber, byte, (IsA ArgZero byte), TT)
            , (byte, exactNumber, (IsA ArgOne byte), TT)
            , (exactNumber, index, (IsA ArgZero index), TT)
            , (index, exactNumber, (IsA ArgOne index), TT)
            , (exactNumber, fixnum, (IsA ArgZero fixnum), TT)
            , (fixnum, exactNumber, (IsA ArgOne fixnum), TT)
            , (exactNumber, integer, (IsA ArgZero integer), TT)
            , (integer, exactNumber, (IsA ArgOne integer), TT)
            , (exactNumber, positiveRational, (IsA ArgZero positiveRational), TT)
            , (positiveRational, exactNumber, (IsA ArgOne positiveRational), TT)
            , (exactNumber, nonnegativeRational, (IsA ArgZero nonnegativeRational), TT)
            , (nonnegativeRational, exactNumber, (IsA ArgOne nonnegativeRational), TT)
            , (exactNumber, negativeRational, (IsA ArgZero negativeRational), TT)
            , (negativeRational, exactNumber, (IsA ArgOne negativeRational), TT)
            , (exactNumber, nonpositiveRational, (IsA ArgZero nonpositiveRational), TT)
            , (nonpositiveRational, exactNumber, (IsA ArgOne nonpositiveRational), TT)
            , (exactNumber, rational, (IsA ArgZero rational), TT)
            , (rational, exactNumber, (IsA ArgOne rational), TT)
            , (real, positiveReal, (IsA ArgZero positiveReal), TT)
            , (positiveReal, real, (IsA ArgOne positiveReal), TT)
            , (real, nonnegativeReal, (IsA ArgZero nonnegativeReal), TT)
            , (nonnegativeReal, real, (IsA ArgOne nonnegativeReal), TT)
            , (real, negativeReal, (IsA ArgZero negativeReal), TT)
            , (negativeReal, real, (IsA ArgOne negativeReal), TT)
            , (real, nonpositiveReal, (IsA ArgZero nonpositiveReal), TT)
            , (nonpositiveReal, real, (IsA ArgOne nonpositiveReal), TT)
            , (number, number, TT, TT)]))

  ] -- end of opTypes
