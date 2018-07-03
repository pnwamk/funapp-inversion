module Types.SyntacticOpTypes where

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

decType :: [(Ty, Ty)]
decType = []

-- [sub1 (from-cases
--        (-> -One -Zero)
--        (-> -PosByte -Byte)
--        (-> -PosIndex -Index)
--        (-> -Index -Fixnum)
--        (-> -PosFixnum -NonNegFixnum)
--        (-> -NonNegFixnum -Fixnum)
--        (-> -Pos -Nat)
--        (-> -NonPosInt -NegInt)
--        (unop -Int)
--        (-> -NonPosRat -NegRat)
--        (unop -Rat)
--        (-> -NonPosFlonum -NegFlonum)
--        (unop -Flonum)
--        (-> -NonPosSingleFlonum -NegSingleFlonum)
--        (unop -SingleFlonum)
--        (-> -NonPosInexactReal -NegInexactReal)
--        (unop -InexactReal)
--        (-> -NonPosReal -NegReal)
--        (map unop (list -Real -FloatComplex -SingleFlonumComplex -InexactComplex N)))]

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


multType :: [(Ty, Ty, Ty)]
multType = []

-- [* (from-cases
--     (-> -One)
--     (-> N N : -true-propset : (-arg-path 0))
--     (commutative-case -Zero N -Zero)
--     (-> N -One N : -true-propset : (-arg-path 0))
--     (-> -One N N : -true-propset : (-arg-path 1))
--     (-> -PosByte -PosByte -PosIndex)
--     (-> -Byte -Byte -Index)
--     (-> -PosByte -PosByte -PosByte -PosFixnum)
--     (-> -Byte -Byte -Byte -NonNegFixnum)
--     (varop -PosInt)
--     (varop -Nat)
--     (-> -NegInt -NegInt)
--     (-> -NonPosInt -NonPosInt)
--     (-> -NegInt -NegInt -PosInt)
--     (commutative-binop -NegInt -PosInt -NegInt)
--     (-> -NonPosInt -NonPosInt -Nat)
--     (commutative-binop -NonPosInt -Nat -NonPosInt)
--     (-> -NegInt -NegInt -NegInt -NegInt)
--     (-> -NonPosInt -NonPosInt -NonPosInt -NonPosInt)
--     (map varop (list -Int -PosRat -NonNegRat))
--     (-> -NegRat -NegRat)
--     (-> -NonPosRat -NonPosRat)
--     (-> -NegRat -NegRat -PosRat)
--     (commutative-binop -NegRat -PosRat -NegRat)
--     (-> -NonPosRat -NonPosRat -NonNegRat)
--     (commutative-binop -NonPosRat -NonNegRat -NonPosRat)
--     (-> -NegRat -NegRat -NegRat -NegRat)
--     (-> -NonPosRat -NonPosRat -NonPosRat -NonPosRat)
--     (varop -Rat)
--     (varop-1+ -FlonumZero)
--     ; no pos * -> pos, possible underflow
--     (varop-1+ -NonNegFlonum)
--     ;; can't do NonPos NonPos -> NonNeg: (* -1.0 0.0) -> NonPos!
--     (-> -NegFlonum -NegFlonum -NonNegFlonum) ; possible underflow, so no neg neg -> pos
--     (-> -NegFlonum -NegFlonum -NegFlonum -NonPosFlonum) ; see above
--     ;; limited flonum contagion rules
--     ;; (* <float> 0) is exact 0 (i.e. not a float)
--     (commutative-case -NonNegFlonum -PosReal) ; real args don't include 0
--     (commutative-case -Flonum (Un -PosReal -NegReal) -Flonum)
--     (map varop-1+ (list -Flonum -SingleFlonumZero -NonNegSingleFlonum))
--     ;; we could add contagion rules for negatives, but we haven't for now
--     (-> -NegSingleFlonum -NegSingleFlonum -NonNegSingleFlonum) ; possible underflow, so no neg neg -> pos
--     (-> -NegSingleFlonum -NegSingleFlonum -NegSingleFlonum -NonPosSingleFlonum)
--     (commutative-case -NonNegSingleFlonum (Un -PosRat -NonNegSingleFlonum))
--     (commutative-case -SingleFlonum (Un -PosRat -NegRat -SingleFlonum) -SingleFlonum)
--     (map varop-1+ (list -SingleFlonum -InexactRealZero -NonNegInexactReal))
--     (-> -NegInexactReal -NegInexactReal -NonNegInexactReal)
--     (-> -NegInexactReal -NegInexactReal -NegInexactReal -NonPosInexactReal)
--     (commutative-case -NonNegInexactReal (Un -PosRat -NonNegInexactReal))
--     (commutative-case -InexactReal (Un -PosRat -NegRat -InexactReal) -InexactReal)
--     (varop-1+ -InexactReal)
--     ;; reals
--     (varop -NonNegReal) ; (* +inf.0 0.0) -> +nan.0
--     (-> -NonPosReal -NonPosReal -NonNegReal)
--     (commutative-binop -NonPosReal -NonNegReal -NonPosReal)
--     (-> -NonPosReal -NonPosReal -NonPosReal -NonPosReal)
--     (varop -Real)
--     ;; complexes
--     (commutative-case -FloatComplex (Un -InexactComplex -InexactReal -PosRat -NegRat) -FloatComplex)
--     (commutative-case -SingleFlonumComplex (Un -SingleFlonumComplex -SingleFlonum -PosRat -NegRat) -SingleFlonumComplex)
--     (commutative-case -InexactComplex (Un -InexactComplex -InexactReal -PosRat -NegRat) -InexactComplex)
--     (varop N))]



divType :: [(Ty, Ty, Ty)]
divType = []

-- [/ (from-cases ; very similar to multiplication, without closure properties for integers
--     (commutative-case -Zero N -Zero)
--     (unop -One)
--     (-> N -One N : -true-propset : (-arg-path 0))
--     (varop-1+ -PosRat)
--     (varop-1+ -NonNegRat)
--     (-> -NegRat -NegRat)
--     (-> -NonPosRat -NonPosRat)
--     (-> -NegRat -NegRat -PosRat)
--     (commutative-binop -NegRat -PosRat -NegRat)
--     (-> -NonPosRat -NonPosRat -NonNegRat)
--     (commutative-binop -NonPosRat -NonNegRat -NonPosRat)
--     (-> -NegRat -NegRat -NegRat -NegRat)
--     (-> -NonPosRat -NonPosRat -NonPosRat -NonPosRat)
--     (varop-1+ -Rat)
--     (-> -FlonumZero (Un -PosFlonum -NegFlonum)) ; one of the infinities
--     ;; No (-> -NonNegFlonum -NonNegFlonum -NonNegFlonum), (/ 0.1 -0.0) => -inf.0
--     ;; No (-> -NonPosFlonum -NonPosFlonum), (/ 0.0) => +inf.0
--     (-> -NegFlonum -NegFlonum -NonNegFlonum)
--     (-> -NegFlonum -NegFlonum -NegFlonum -NonPosFlonum)
--     ;; limited flonum contagion rules
--     ;; (/ 0 <float>) is exact 0 (i.e. not a float)
--     (commutative-case -PosFlonum -PosReal -NonNegFlonum)
--     (->* (list (Un -PosReal -NegReal -Flonum) -Flonum) -Flonum -Flonum)
--     (->* (list -Flonum) -Real -Flonum) ; if any argument after the first is exact 0, not a problem
--     (varop-1+ -Flonum)
--     (-> -SingleFlonumZero (Un -PosSingleFlonum -NegSingleFlonum)) ; one of the infinities
--     ;; we could add contagion rules for negatives, but we haven't for now
--     (-> -NegSingleFlonum -NegSingleFlonum -NonNegSingleFlonum) ; possible underflow, so no neg neg -> pos
--     (-> -NegSingleFlonum -NegSingleFlonum -NegSingleFlonum -NonPosSingleFlonum)
--     (commutative-case -PosSingleFlonum (Un -PosRat -PosSingleFlonum) -NonNegSingleFlonum)
--     (commutative-case -SingleFlonum (Un -PosRat -NegRat -SingleFlonum) -SingleFlonum)
--     (varop-1+ -SingleFlonum)
--     (-> -InexactRealZero (Un -PosInexactReal -NegInexactReal))
--     (-> -NegInexactReal -NegInexactReal -NonNegInexactReal)
--     (-> -NegInexactReal -NegInexactReal -NegInexactReal -NonPosInexactReal)
--     (commutative-case -PosInexactReal (Un -PosRat -PosInexactReal) -NonNegInexactReal)
--     (commutative-case -InexactReal (Un -PosRat -NegRat -InexactReal) -InexactReal)
--     (varop-1+ -InexactReal)
--     ;; reals
--     (varop-1+ -PosReal -NonNegReal)
--     (-> -NonPosReal -NonPosReal)
--     (-> -NegReal -NegReal -NonNegReal) ; 0.0 is non-neg, but doesn't preserve sign
--     (-> -NegReal -PosReal -NonPosReal) ; idem
--     (-> -PosReal -NegReal -NonPosReal) ; idem
--     (-> -NegReal -NegReal -NegReal -NonPosReal) ; idem
--     (varop-1+ -Real)
--     ;; complexes
--     (varop-1+ -FloatComplex)
--     (commutative-case -FloatComplex (Un -InexactComplex -InexactReal -PosRat -NegRat) -FloatComplex)
--     (->* (list -FloatComplex) N -FloatComplex) ; if any argument after the first is exact 0, not a problem
--     (varop-1+ -SingleFlonumComplex)
--     (commutative-case -SingleFlonumComplex (Un -SingleFlonumComplex -SingleFlonum -PosRat -NegRat) -SingleFlonumComplex)
--     (varop-1+ -InexactComplex)
--     (commutative-case -InexactComplex (Un -InexactComplex -InexactReal -PosRat -NegRat) -InexactComplex)
--     (varop-1+ N))]

modType :: [(Ty, Ty, Ty)]
modType = []

-- [modulo ; result has same sign as second arg
--  (from-cases
--   (-One -One . -> . -Zero)
--   (map (lambda (t) (list (-> -Int t t)
--                          (-> t -Nat t)))
--        (list -Byte -Index -NonNegFixnum -Nat))
--   (-Int -NonPosFixnum . -> . -NonPosFixnum)
--   (-Int -NonPosInt . -> . -NonPosInt)
--   (commutative-binop -Fixnum -Int)
--   (binop -Int))]

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
         , (integer, positiveRealNoNaN, TT, (IsA ArgZero positiveInteger)) -- AMK added NoNaN
         , (integer, nonnegativeRealNoNaN, TT, (IsA ArgZero nonnegativeInteger)) -- AMK added NoNaN
         , (nonnegativeReal, integer, (IsA ArgOne positiveInteger), TT)
         , (integer, nonpositiveReal, (IsA ArgZero negativeInteger), TT)
         , (negativeRealNoNaN, integer, TT, (IsA ArgOne negativeInteger)) -- AMK added NoNaN
         , (nonpositiveRealNoNaN, integer, TT, (IsA ArgOne nonpositiveInteger)) -- AMK added NoNaN
         -- <-type-pattern rational
         , (rational, zero, (IsA ArgZero negativeRational), (IsA ArgZero nonnegativeRational))
         , (zero, rational, (IsA ArgOne positiveRational), (IsA ArgOne nonpositiveRational))
         , (rational, positiveRealNoNaN, TT, (IsA ArgZero positiveRational)) -- AMK added NoNaN
         , (rational, nonnegativeRealNoNaN, TT, (IsA ArgZero nonnegativeRational)) -- AMK added NoNaN
         , (nonnegativeReal, rational, (IsA ArgOne positiveRational), TT)
         , (rational, nonpositiveReal, (IsA ArgZero negativeRational), TT)
         , (negativeRealNoNaN, rational, TT, (IsA ArgOne negativeRational)) -- AMK added NoNaN
         , (nonpositiveRealNoNaN, rational, TT, (IsA ArgOne nonpositiveRational)) -- AMK added NoNaN
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


leqType :: [(Ty, Ty, Prop, Prop)]
leqType = []

-- [<= (from-cases
--      (-> -Int -One B : (-PS (-is-type 0 (Un -NonPosInt -One)) (-is-type 0 -PosInt)))
--      (-> -One -Int B : (-PS (-is-type 1 -PosInt) (-is-type 1 -NonPosInt)))
--      (-> -Real -Zero B : (-PS (-is-type 0 -NonPosReal) (-is-type 0 -PosReal)))
--      (-> -Zero -Real B : (-PS (-is-type 1 -NonNegReal) (-is-type 1 -NegReal)))
--      (-> -Real -RealZero B : (-PS (-is-type 0 -NonPosReal) -tt)) ;; False says nothing because of NaN
--      (-> -RealZero -Real B : (-PS (-is-type 0 -NonNegReal) -tt)) ;; False says nothing because of NaN
--      (-> -PosByte -Byte B : (-PS (-is-type 1 -PosByte) -tt))
--      (-> -Byte -Byte B : (-PS -tt (-is-type 0 -PosByte)))
--      (-> -PosInt -Byte B : (-PS (-and (-is-type 0 -PosByte) (-is-type 1 -PosByte)) -tt))
--      (-> -PosReal -Byte B : (-PS (-is-type 1 -PosByte) -tt))
--      (-> -Byte -PosInt B : (-PS -tt (-and (-is-type 0 -PosByte) (-is-type 1 -PosByte))))
--      (-> -Byte -PosRat B : (-PS -tt (-is-type 0 -PosByte)))
--      (-> -Nat -Byte B : (-PS (-is-type 0 -Byte) -tt))
--      (-> -Byte -Nat B : (-PS -tt (-and (-is-type 0 -PosByte) (-is-type 1 -Byte))))
--      (-> -Byte -NonNegRat B : (-PS -tt (-is-type 0 -PosByte)))
--      (-> -PosIndex -Index B : (-PS (-is-type 1 -PosIndex) -tt))
--      (-> -Index -Index B : (-PS -tt (-is-type 0 -PosIndex)))
--      (-> -Pos -Index B : (-PS (-and (-is-type 0 -PosIndex) (-is-type 1 -PosIndex)) -tt))
--      (-> -PosReal -Index B : (-PS (-is-type 1 -PosIndex) -tt))
--      (-> -Index -Pos B : (-PS -tt (-and (-is-type 0 -PosIndex) (-is-type 1 -PosIndex))))
--      (-> -Index -PosRat B : (-PS -tt (-is-type 0 -PosIndex)))
--      (-> -Nat -Index B : (-PS (-is-type 0 -Index) -tt))
--      (-> -Index -Nat B : (-PS -tt (-and (-is-type 0 -PosIndex) (-is-type 1 -Index))))
--      (-> -Index -NonNegRat B : (-PS -tt (-is-type 0 -PosIndex)))
--      (-> -PosInt -Fixnum B : (-PS (-and (-is-type 0 -PosFixnum) (-is-type 1 -PosFixnum)) -tt))
--      (-> -PosReal -Fixnum B : (-PS (-is-type 1 -PosFixnum) -tt))
--      (-> -Nat -Fixnum B : (-PS (-and (-is-type 0 -NonNegFixnum) (-is-type 1 -NonNegFixnum)) -tt))
--      (-> -NonNegReal -Fixnum B : (-PS (-is-type 1 -NonNegFixnum) -tt))
--      (-> -Fixnum -Nat B : (-PS -tt (-and (-is-type 0 -PosFixnum) (-is-type 1 -NonNegFixnum))))
--      (-> -Fixnum -NonNegRat B : (-PS -tt (-is-type 0 -PosFixnum)))
--      (-> -NonPosInt -Fixnum B : (-PS -tt (-and (-is-type 0 -NonPosFixnum) (-is-type 1 -NegFixnum))))
--      (-> -NonPosRat -Fixnum B : (-PS -tt (-is-type 1 -NegFixnum)))
--      (-> -Fixnum -NegInt B : (-PS (-and (-is-type 0 -NegFixnum) (-is-type 1 -NegFixnum)) -tt))
--      (-> -Fixnum -NegReal B : (-PS (-is-type 0 -NegFixnum) -tt))
--      (-> -Fixnum -NonPosInt B : (-PS (-and (-is-type 0 -NonPosFixnum) (-is-type 1 -NonPosFixnum)) -tt))
--      (-> -Fixnum -NonPosReal B : (-PS (-is-type 0 -NonPosFixnum) -tt))
--      (-> -Real -PosInfinity B : (-PS (-not-type 0 -InexactRealNan) (-is-type 0 -InexactRealNan)))
--      (-> -NegInfinity -Real B : (-PS (-not-type 1 -InexactRealNan) (-is-type 1 -InexactRealNan)))
--      (-> -PosInfinity -Real B : (-PS (-is-type 1 -PosInfinity) (-not-type 1 -PosInfinity)))
--      (-> -Real -NegInfinity B : (-PS (-is-type 0 -NegInfinity) (-not-type 0 -NegInfinity)))
--      (<=-type-pattern -Int -PosInt -Nat -NegInt -NonPosInt -Zero)
--      (<=-type-pattern -Rat -PosRat -NonNegRat -NegRat -NonPosRat -Zero)
--      (<=-type-pattern -Flonum -PosFlonum -NonNegFlonum -NegFlonum -NonPosFlonum #:no-false-props? #t)
--      (<=-type-pattern -SingleFlonum -PosSingleFlonum -NonNegSingleFlonum -NegSingleFlonum -NonPosSingleFlonum #:no-false-props? #t)
--      (<=-type-pattern -InexactReal -PosInexactReal -NonNegInexactReal -NegInexactReal -NonPosInexactReal #:no-false-props? #t)
--      (<=-type-pattern -Real -PosReal -NonNegReal -NegReal -NonPosReal #:no-false-props? #t)
--      (->* (list R R) R B))]

eqType :: [(Ty, Ty, Prop, Prop)]
eqType = []


-- [=
--  (from-cases
--    (-> -Real -RealZero B : (-PS (-is-type 0 -RealZeroNoNan) (-not-type 0 -RealZeroNoNan)))
--    (-> -RealZero -Real B : (-PS (-is-type 1 -RealZeroNoNan) (-not-type 1 -RealZeroNoNan)))
--   (map (lambda (t) (commutative-equality/prop -ExactNumber t))
--        (list -One -PosByte -Byte -PosIndex -Index
--              -PosFixnum -NonNegFixnum -NegFixnum -NonPosFixnum -Fixnum
--              -PosInt -Nat -NegInt -NonPosInt -Int
--              -PosRat -NonNegRat -NegRat -NonPosRat -Rat
--              -ExactNumber))
--   ;; For all real types: the props give sign information, and the exactness information is preserved
--   ;; from the original types.
--   (map (lambda (t) (commutative-equality/prop -Real t))
--        (list -RealZero -PosReal -NonNegReal -NegReal -NonPosReal -Real))
--   (->* (list N N) N B))]

