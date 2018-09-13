module Types.SyntacticOpTypesPlus where

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
              , (nonposFixnum, fixnum)
              , (negInteger, nonposInteger)
              , (nonnegReal, posReal)
              , (real, real)
              , (inexactReal, inexactReal)
              , (inexactComplex, inexactComplex)
              , (number, number)]))
    
  , ("sub1", (UnOp
              [ (one, zero)
              , (posByte, byte)
              , (posIndex, index)
              , (nonnegFixnum, fixnum)
              , (posInteger, nonnegInteger)
              , (integer, integer)
              , (rational, rational)
              , (float, float)
              , (singleFloat, singleFloat)
              , (inexactReal, inexactReal)
              , (nonposReal, negReal)
              , (real, real)
              , (floatComplex, floatComplex)
              , (singleFloatComplex, singleFloatComplex)
              , (inexactComplex, inexactComplex)
              , (number, number)]))
    
  , ("abs", (UnOp
             [ (realZero, realZero)
             , (integer, nonnegInteger)
             , (rational, nonnegRational)
             , (float, nonnegFloat)
             , (singleFloat, nonnegSingleFloat)
             , (inexactReal, nonnegInexactReal)
             , ((tyOr' [posReal, negReal]), posReal)
             , (real, nonnegReal)]))

  , ("sqr", (UnOp [ (zero, zero)
                  , (one, one)
                  , (byte, index)
                  , (integer, nonnegInteger)
                  , (posRational, posRational)
                  , (float, nonnegFloat)
                  , (singleFloat, nonnegSingleFloat)
                  , (inexactReal, nonnegInexactReal)
                  , (real, nonnegReal)
                  , (floatComplex, floatComplex)
                  , (singleFloatComplex, singleFloatComplex)
                  , (inexactComplex, inexactComplex)
                  , (exactNumber, exactNumber)
                  , (number, number)]))
      
  , ("sqrt", (UnOp [ (zero, zero)
                   , (one, one)
                   , (nonnegFloat, nonnegFloat)
                   , (nonnegSingleFloat, nonnegSingleFloat)
                   , (inexactRealPosZero, inexactRealPosZero)
                   , (inexactRealNegZero, inexactRealNegZero)
                   , (nonnegInexactReal, nonnegInexactReal)
                   , (realZero, realZero)
                   , (posReal, posReal)
                   , (nonnegReal, nonnegReal)
                   , (floatComplex, floatComplex)
                   , (singleFloatComplex, singleFloatComplex)
                   , (inexactComplex, inexactComplex)
                   , (number, number)]))

  , ("expt", (BinOp [ (one, rational, one)
                    , (number, zero, one) -- will error if neg
                    , (integer, nonnegInteger, integer)
                    , (posRational, integer, posRational)
                    , (nonnegRational, integer, nonnegRational)
                    , (rational, integer, rational)
                    , (nonnegFloat, real, (tyOr nonnegFloat one))
                    , (posReal, nonnegFloat, (tyOr nonnegFloat one))
                    , (float, fixnum, (tyOr float one))
                    , (float, float, (tyOr float floatComplex))
                    , (nonnegSingleFloat, (tyOr' [singleFloat, negFixnum, posFixnum]), singleFloat)
                    , (singleFloat, fixnum, (tyOr singleFloat one))
                    , (singleFloat, singleFloat, (tyOr singleFloat singleFloatComplex))
                    , (posReal, real, nonnegReal)
                    , (nonnegReal, real, real)
                    , (inexactReal, (tyOr negFixnum posFixnum), inexactReal)
                    , (inexactReal, inexactReal, (tyOr inexactReal inexactComplex))
                    , (real, nonnegInteger, real)
                    , (floatComplex, float, (tyOr floatComplex float))
                    , (floatComplex, inexactReal, (tyOr floatComplex inexactReal))
                    , (floatComplex, inexactComplex, floatComplex)
                    , (singleFloatComplex, singleFloatComplex, singleFloatComplex)
                    , (singleFloatComplex, singleFloat, (tyOr singleFloatComplex singleFloat))
                    , (inexactComplex, inexactComplex, inexactComplex)
                    , (number, number, number)]))
  
  , ("modulo", (BinOp [ (one, one, zero)
                      , (integer, byte, byte)
                      , (byte, nonnegInteger, byte)
                      , (integer, index, index)
                      , (index, nonnegInteger, index)
                      , (nonnegFixnum, nonnegInteger, nonnegFixnum)
                      , (integer, nonnegInteger, nonnegInteger)
                      , (integer, nonposInteger, nonposInteger)
                      , (integer, fixnum, fixnum)
                      , (integer, integer, integer)]))
  
  , ("quotient", (BinOp [ (zero, integer, zero)
                        , (posFixnum, one, posFixnum)
                        , (negFixnum, one, negFixnum)
                        , (fixnum, one, fixnum)
                        , (byte, nonnegInteger, byte)
                        , (index, nonnegInteger, index)
                        , (nonposFixnum, nonnegFixnum, nonposFixnum)
                        , (nonnegFixnum, integer, fixnum)
                        , (nonnegInteger, nonnegInteger, nonnegInteger)
                        , (nonnegInteger, nonposInteger, nonposInteger)
                        , (nonposInteger, nonnegInteger, nonposInteger)
                        , (nonposInteger, nonposInteger, nonnegInteger)
                        , (integer, integer, integer)]))

  , ("+", (BinOp
            [ (byte, byte, index)
            , (index, index, nonnegFixnum)
            , (negFixnum, one, nonposFixnum)
            , (one, negFixnum, nonposFixnum)
            , (nonposFixnum, nonnegFixnum, fixnum)
            , (nonnegFixnum, nonposFixnum, fixnum)
            , (integer, integer, integer)
            , (float, real, float)
            , (real, float, float)
            , (singleFloat, (tyOr' [rational, singleFloat]), singleFloat)
            , ((tyOr' [rational, singleFloat]), singleFloat, singleFloat)
            , (inexactReal, real, inexactReal)
            , (real, inexactReal, inexactReal)
            , (posReal, nonnegReal, posReal)
            , (nonnegReal, posReal, posReal)
            , (negReal, nonposReal, negReal)
            , (nonposReal, negReal, negReal)
            , (nonnegReal, nonnegReal, nonnegReal)
            , (nonposReal, nonposReal, nonposReal)
            , (real, real, real)
            , (exactNumber, exactNumber, exactNumber)
            , (floatComplex, number, floatComplex)
            , (number, floatComplex, floatComplex)
            , (float, inexactComplex, floatComplex)
            , (inexactComplex, float, floatComplex)
            , (singleFloatComplex, (tyOr' [rational, singleFloat, singleFloatComplex]), singleFloatComplex)
            , ((tyOr' [rational, singleFloat, singleFloatComplex]), singleFloatComplex, singleFloatComplex)
            , (inexactComplex, (tyOr' [rational, inexactReal, inexactComplex]), inexactComplex)
            , ((tyOr' [rational, inexactReal, inexactComplex]), inexactComplex, inexactComplex)
            , (number, number, number)])) 
    
  , ("-", (BinOp
            [ (zero, posReal, negReal) -- negation pattern
            , (zero, nonnegReal, nonposReal) -- negation pattern
            , (zero, negReal, posReal) -- negation pattern
            , (zero, nonposReal, nonnegReal) -- negation pattern
            , (one, one, zero)
            , (posByte, one, byte)
            , (posIndex, one, index)
            , (posInteger, one, nonnegInteger)
            , (nonnegFixnum, nonnegFixnum, fixnum)
            , (negFixnum, nonposFixnum, fixnum)
            , (integer, integer, integer)
            , (posRational, nonposRational, posRational)
            , (nonnegRational, nonposRational, nonnegRational)
            , (negRational, nonnegRational, negRational)
            , (nonposRational, nonnegRational, nonposRational)
            , (float, real, float)
            , (real, float, float)
            , (singleFloat, (tyOr' [singleFloat, rational]), singleFloat)
            , ((tyOr' [singleFloat, rational]), singleFloat, singleFloat)
            , (inexactReal, (tyOr' [inexactReal, rational]), inexactReal)
            , ((tyOr' [inexactReal, rational]), inexactReal, inexactReal)
            , (real, real, real)
            , (exactNumber, exactNumber, exactNumber)
            , (floatComplex, number, floatComplex)
            , (number, floatComplex, floatComplex)
            , (singleFloatComplex, (tyOr' [singleFloatComplex, exactNumber]), singleFloatComplex)
            , ((tyOr' [singleFloatComplex, exactNumber]), singleFloatComplex, singleFloatComplex)
            , (inexactComplex, (tyOr' [inexactComplex, exactNumber]), inexactComplex)
            , ((tyOr' [inexactComplex, exactNumber]), inexactComplex, inexactComplex)
            , (number, number, number)]))

  , ("*", (BinOp
            [ (zero, number, zero)
            , (number, zero, zero)
            , (byte, byte, index)
            , (integer, integer, integer)
            , (tyAnd' [rational, (tyNot zero)], tyAnd' [rational, (tyNot zero)], tyAnd' [rational, (tyNot zero)])
            , (rational, rational, rational)
            , (float, (tyOr' [posReal, negReal]), float)
            , ((tyOr' [posReal, negReal]), float, float)
            , (float, float, float)
            , (singleFloat, (tyOr' [posRational, negRational, singleFloat]), singleFloat)
            , ((tyOr' [posRational, negRational, singleFloat]), singleFloat, singleFloat)
            , (inexactReal, (tyOr' [posRational, negRational, inexactReal]), inexactReal)
            , ((tyOr' [posRational, negRational, inexactReal]), inexactReal, inexactReal)
            , (nonnegReal, nonnegReal, nonnegReal) -- (* +inf.0 0.0) -> +nan.0
            , (nonposReal, nonposReal, nonnegReal)
            , (nonposReal, nonnegReal, nonposReal)
            , (nonnegReal, nonposReal, nonposReal)
            , (real, real, real)
            , (floatComplex, (tyOr' [inexactComplex, inexactReal, posRational, negRational]), floatComplex)
            , ((tyOr' [inexactComplex, inexactReal, posRational, negRational]), floatComplex, floatComplex)
            , (singleFloatComplex, (tyOr' [singleFloatComplex, singleFloat, posRational, negRational]), singleFloatComplex)
            , ((tyOr' [singleFloatComplex, singleFloat, posRational, negRational]), singleFloatComplex, singleFloatComplex)
            , (inexactComplex, (tyOr' [inexactComplex, inexactReal, posRational, negRational]), inexactComplex)
            , ((tyOr' [inexactComplex, inexactReal, posRational, negRational]), inexactComplex, inexactComplex)
            , (number, number, number)]))

  , ("/", (BinOp
            [ (number, zero, emptyTy)
            , (zero, number, zero)
            , (one, one, one)
            , (nonnegRational, nonnegRational, nonnegRational)
            , (nonposRational, nonposRational, nonnegRational)
            , (nonposRational, nonnegRational, nonposRational)
            , (nonnegRational, nonposRational, nonposRational)
            , (tyAnd' [rational, (tyNot zero)], tyAnd' [rational, (tyNot zero)], tyAnd' [rational, (tyNot zero)])
            , (rational, rational, rational)
            , ((tyOr' [posReal, negReal, float]), float, float)
            , (float, real, float) -- if any argument after the first is exact 0, not a problem
            , (singleFloat, (tyOr' [posRational, negRational, singleFloat]), singleFloat)
            , ((tyOr' [posRational, negRational, singleFloat]), singleFloat, singleFloat)
            , (inexactReal, (tyOr' [posRational, negRational, inexactReal]), inexactReal)
            , ((tyOr' [posRational, negRational, inexactReal]), inexactReal, inexactReal)
            , (posReal, posReal, nonnegReal)
            , (negReal, negReal, nonnegReal) -- 0.0 is non-neg, but doesn't preserve sign
            , (negReal, posReal, nonposReal) -- idem
            , (posReal, negReal, nonposReal) -- idem
            , (real, real, real)
            , ((tyOr' [inexactComplex, inexactReal, posRational, negRational]), floatComplex, floatComplex)
            , (floatComplex, number, floatComplex) -- if any argument after the first is exact 0, not a problem
            , (singleFloatComplex, (tyOr' [singleFloatComplex, singleFloat, posRational, negRational]), singleFloatComplex)
            , ((tyOr' [singleFloatComplex, singleFloat, posRational, negRational]), singleFloatComplex, singleFloatComplex)
            , (inexactComplex, (tyOr' [inexactComplex, inexactReal, posRational, negRational]), inexactComplex)
            , ((tyOr' [inexactComplex, inexactReal, posRational, negRational]), inexactComplex, inexactComplex)
            , (number, number, number)]))

  , ("max", (BinOp
              [ (one, one, one)
              , (one, zero, one)
              , (zero, one, one)
              , (posByte, byte, posByte)
              , (byte, posByte, posByte)
              , (index, index, index)
              , (fixnum, fixnum, fixnum)
              , (integer, integer, integer)
              , (rational, rational, rational)
              , (float, float, float)
              , (singleFloat, singleFloat, singleFloat)
              , (inexactRealPosZero, inexactRealPosZero, inexactRealPosZero)
              , (inexactRealNegZero, inexactRealNegZero, inexactRealNegZero)
              , (inexactReal, inexactReal, inexactReal)
              , (posReal, real, posReal)
              , (real, posReal, posReal)
              , (nonnegReal, real, nonnegReal)
              , (real, nonnegReal, nonnegReal)
              , (negReal, negReal, negReal)
              , (nonposReal, nonposReal, nonposReal)
              , (real, real, real)]))

  , ("min", (BinOp
              [ (one, one, one)
              , (index, index, index)
              , (byte, nonnegInteger, byte)
              , (nonnegInteger, byte, byte)
              , (nonnegFixnum, nonnegInteger, nonnegFixnum)
              , (nonnegInteger, nonnegFixnum, nonnegFixnum)
              , (fixnum, fixnum, fixnum)
              , (integer, integer, integer)
              , (rational, rational, rational)
              , (float, float, float)
              , (singleFloat, singleFloat, singleFloat)
              , (inexactRealPosZero, inexactRealPosZero, inexactRealPosZero)
              , (inexactRealNegZero, inexactRealNegZero, inexactRealNegZero)
              , (inexactReal, inexactReal, inexactReal)
              , (posReal, posReal, posReal)
              , (nonnegReal, nonnegReal, nonnegReal)
              , (negReal, real, negReal)
              , (real, negReal, negReal)
              , (nonposReal, real, nonposReal)
              , (real, nonposReal, nonposReal)
              , (real, real, real)]))

    
  , ("<", (CompOp
           [ (integer, one, (IsA ArgZero nonposInteger), (IsA ArgZero posInteger))
           , (real, zero, (IsA ArgZero negReal), (IsA ArgZero nonnegReal))
           , (zero, real, (IsA ArgOne posReal), (IsA ArgOne nonposReal))
           , (nonnegInteger, byte, (Conj (IsA ArgZero byte) (IsA ArgOne posByte)), TT)
           , (byte, nonnegInteger, TT, (IsA ArgOne byte))
           , (nonnegInteger, index, (Conj (IsA ArgZero index) (IsA ArgOne posIndex)), TT)
           , (index, nonnegInteger, TT, (IsA ArgOne index))
           , (fixnum, nonnegInteger, TT, (Conj (IsA ArgZero nonnegFixnum) (IsA ArgOne nonnegFixnum)))
           , (nonnegInteger, fixnum, (Conj (IsA ArgZero nonnegFixnum) (IsA ArgOne posFixnum)), TT)
           , (fixnum, nonposInteger, (Conj (IsA ArgZero negFixnum) (IsA ArgOne nonposFixnum)), TT)
           , (nonposInteger, fixnum, TT, (Conj (IsA ArgZero nonposFixnum) (IsA ArgOne nonposFixnum)))
           , (real, posInfinity, (IsA ArgZero (tyNot (tyOr' [inexactRealNaN, posInfinity]))), (IsA ArgZero (tyOr' [inexactRealNaN, posInfinity])))
           , (negInfinity, real, (IsA ArgOne (tyNot (tyOr' [inexactRealNaN, negInfinity]))), (IsA ArgOne (tyOr' [inexactRealNaN, negInfinity])))
           , (posInfinity, real, FF, TT)
           , (real, negInfinity, FF, TT)
           , (rational, posRealNoNaN, TT, (IsA ArgZero posRational)) -- AMK added NoNaN
           , (rational, nonnegRealNoNaN, TT, (IsA ArgZero nonnegRational)) -- AMK added NoNaN
           , (negRealNoNaN, rational, TT, (IsA ArgOne negRational)) -- AMK added NoNaN
           , (nonposRealNoNaN, rational, TT, (IsA ArgOne nonposRational)) -- AMK added NoNaN
           , (nonnegReal, real, (IsA ArgOne posReal), TT)
           , (real, nonposReal, (IsA ArgZero negReal), TT)
           , (real, real, TT, TT)]))
    
  , ("<=", (CompOp
             [ (integer, one, (IsA ArgZero (tyOr' [nonposInteger, one])), (IsA ArgZero posInteger))
             , (one, integer, (IsA ArgOne posInteger), (IsA ArgOne nonposInteger))
             , (real, zero, (IsA ArgZero nonposReal), (IsA ArgZero posReal))
             , (zero, real, (IsA ArgOne nonnegReal), (IsA ArgOne negReal))
             , (nonnegInteger, byte, (IsA ArgZero byte), TT)
             , (byte, nonnegInteger, TT, (Conj (IsA ArgZero posByte) (IsA ArgOne byte)))
             , (nonnegInteger, index, (IsA ArgZero index), TT)
             , (index, nonnegInteger, TT, (Conj (IsA ArgZero posIndex) (IsA ArgOne index)))
             , (nonnegInteger, fixnum, (Conj (IsA ArgZero nonnegFixnum) (IsA ArgOne nonnegFixnum)), TT)
             , (fixnum, nonnegInteger, TT, (Conj (IsA ArgZero posFixnum) (IsA ArgOne nonnegFixnum)))
             , (nonposInteger, fixnum, TT, (Conj (IsA ArgZero nonposFixnum) (IsA ArgOne negFixnum)))
             , (fixnum, nonposInteger, (Conj (IsA ArgZero nonposFixnum) (IsA ArgOne nonposFixnum)), TT)
             , (real, posInfinity, (IsA ArgZero (tyNot inexactRealNaN)), (IsA ArgZero inexactRealNaN))
             , (negInfinity, real, (IsA ArgOne (tyNot inexactRealNaN)), (IsA ArgOne inexactRealNaN))
             , (posInfinity, real, (IsA ArgOne posInfinity), (IsA ArgOne (tyNot posInfinity)))
             , (real, negInfinity, (IsA ArgZero negInfinity), (IsA ArgZero (tyNot negInfinity)))
             , (rational, nonnegRealNoNaN, TT, (IsA ArgZero posRational)) -- <=-pat rational
             , (nonposRealNoNaN, rational, TT, (IsA ArgOne negRational)) -- <=-pat rational
             , (posReal, real, (IsA ArgOne posReal), TT) -- <=-pat real
             , (nonnegReal, real, (IsA ArgOne nonnegReal), TT) -- <=-pat real
             , (real, negReal, (IsA ArgZero negReal), TT) -- <=-pat real
             , (real, nonposReal, (IsA ArgZero nonposReal), TT) -- <=-pat real
             , (real, real, TT, TT)]))

  , ("=", (CompOp
            [ (real, realZero, (IsA ArgZero realZeroNoNaN), (IsA ArgZero (tyNot realZeroNoNaN)))
            , (realZero, real, (IsA ArgOne realZeroNoNaN), (IsA ArgOne (tyNot realZeroNoNaN)))
            , (exactNumber, one, (IsA ArgZero one), (IsA ArgZero (tyNot one)))
            , (one, exactNumber, (IsA ArgOne one), (IsA ArgOne (tyNot one)))
            , (exactNumber, byte, (IsA ArgZero byte), TT)
            , (byte, exactNumber, (IsA ArgOne byte), TT)
            , (exactNumber, index, (IsA ArgZero index), TT)
            , (index, exactNumber, (IsA ArgOne index), TT)
            , (exactNumber, fixnum, (IsA ArgZero fixnum), TT)
            , (fixnum, exactNumber, (IsA ArgOne fixnum), TT)
            , (exactNumber, integer, (IsA ArgZero integer), TT)
            , (integer, exactNumber, (IsA ArgOne integer), TT)
            , (exactNumber, posRational, (IsA ArgZero posRational), TT)
            , (posRational, exactNumber, (IsA ArgOne posRational), TT)
            , (exactNumber, nonnegRational, (IsA ArgZero nonnegRational), TT)
            , (nonnegRational, exactNumber, (IsA ArgOne nonnegRational), TT)
            , (exactNumber, negRational, (IsA ArgZero negRational), TT)
            , (negRational, exactNumber, (IsA ArgOne negRational), TT)
            , (exactNumber, nonposRational, (IsA ArgZero nonposRational), TT)
            , (nonposRational, exactNumber, (IsA ArgOne nonposRational), TT)
            , (exactNumber, rational, (IsA ArgZero rational), TT)
            , (rational, exactNumber, (IsA ArgOne rational), TT)
            , (real, posReal, (IsA ArgZero posReal), TT)
            , (posReal, real, (IsA ArgOne posReal), TT)
            , (real, nonnegReal, (IsA ArgZero nonnegReal), TT)
            , (nonnegReal, real, (IsA ArgOne nonnegReal), TT)
            , (real, negReal, (IsA ArgZero negReal), TT)
            , (negReal, real, (IsA ArgOne negReal), TT)
            , (real, nonposReal, (IsA ArgZero nonposReal), TT)
            , (nonposReal, real, (IsA ArgOne nonposReal), TT)
            , (number, number, TT, TT)]))

  ] -- end of opTypes
