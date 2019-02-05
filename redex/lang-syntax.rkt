#lang racket/base

(require redex/reduction-semantics)

(provide (all-defined-out))


(define-language sot
  ;; SURFACE LEVEL GRAMMAR
  ;; - - - - - - - - - - - -
  [x y z f ::= variable-not-otherwise-mentioned]
  ;; constants
  [nop1 ::= add1 sub1 abs sqr sqrt
        real->double-flonum
        real->single-flonum
        inexact->exact]
  [nop2 ::= + - * / min max < <= = expt quotient modulo]
  ;; primitive ops
  [prim ::= string-length not exact-integer? string? pair? procedure?
          error zero? null? nop1 nop2]
  [const ::= number string boolean null prim]
  [i ::= 1 2]
  ;; expressions
  [I ::= (Set (Arrow τ τ) ... (Arrow τ τ))]
  [e ::= x const (e e) (nop2 e e) (μ(f)I λ(x) e)
     (proj i e) (pair e e) (if e e e) (let (x e) e)]
  ;; numeric expressions (for testing):
  
  ;; numeric base types
  [η ::=
     Zero
     One
     ByteLargerThanOne
     PosIndexNotByte
     PosFixnumNotIndex
     NegFixnum
     PosIntegerNotFixnum
     NegIntegerNotFixnum
     PosRationalNotInteger
     NegRationalNotInteger
     FloatNaN
     FloatPosZero
     FloatNegZero
     PosFloatNumber
     PosFloatInfinity
     NegFloatNumber
     NegFloatInfinity
     SingleFloatNaN
     SingleFloatPosZero
     SingleFloatNegZero
     PosSingleFloatNumber
     PosSingleFloatInfinity
     NegSingleFloatNumber
     NegSingleFloatInfinity
     ExactImaginary
     ExactComplex
     FloatImaginary
     SingleFloatImaginary
     FloatComplex
     SingleFloatComplex]
  ;; base types
  [ι ::= String True False Null η]
  ;; predefined recursive types
  [X ::= ByteList IntList NumList]
  ;; types
  [τ σ ::= ι (Prod τ τ) (Arrow τ τ) (Or τ τ) (And τ τ) (Not τ) Any Empty X]
  ;; misc for typesetting
  [τ-or-& τ &]
  [τ-or-U τ U]
  ;; paths and objects
  [path ::= x (projP i path)]
  [obj  ::= topO botO path]
  ;; props
  [p q ::= (∈ path τ) (∧ p p) (∨ p p) (≡ path path) tt ff]
  [Γ ::= EnvNull (EnvSnoc Γ p)]
  ;; type results
  [R ::= (Res τ p q obj)]
  ;; values
  [v ::= const (pair v v) (closure ρ (μ(f)(Set (Arrow τ τ) ... (Arrow τ τ))λ(x) e))]
  [FAIL ::= ERROR STUCK TIMEOUT]
  [RESULT ::= v FAIL]
  ;; runtime environments
  [ρ ::= RhoNull (RhoSnoc ρ[x ↦ v])]
  [MISC ::= ; None]
  [N ::= (Nat 0) (Nat 1(PLUS)N)]
  ;; internal defs
  [prop-or-Env ::= p Γ]
  
  ;; BINDERS
  ;; - - - - - - - - - - - - - -
  #:binding-forms
  (μ(f)(Set (Arrow τ σ) ...)λ(x) e #:refers-to (shadow f x))
  (let (x e_1) e_2 #:refers-to x))

;; Common type abbrevs
(define-term Boolean (Or True False))
(define-term Any-Pair (Prod Any Any))
(define-term Any-Fun  (Arrow Empty Any))
(define-term Any-Base (Not (Or Any-Pair Any-Fun)))


(define-metafunction sot
  Or* : τ-or-U τ-or-U ... -> τ
  [(Or* any_1 ... any_n)
   ,(for/fold ([acc (term any_n)])
              ([t (in-list (reverse (term (any_1 ...))))]
               #:when (not (eq? t 'U)))
      (term (Or ,t ,acc)))])


(define-metafunction sot
  BigAnd : τ τ ... -> τ
  [(BigAnd any_1 ... any_n)
   ,(for/fold ([acc (term any_n)])
              ([t (in-list (reverse (term (any_1 ...))))])
      (term (And ,t ,acc)))])

(define-metafunction sot
  And* : τ-or-& τ-or-& ... -> τ
  [(And* any_1 ... any_n)
   ,(for/fold ([acc (term any_n)])
              ([t (in-list (reverse (term (any_1 ...))))]
               #:when (not (eq? t '&)))
      (term (And ,t ,acc)))])

(define τ? (redex-match? sot τ))

(define-syntax-rule (define-type-abbreviations
                      #:abbrev-table type-abbrev-names
                      [name def] ...)
  (begin (define type-abbrev-names/defs
           '((name . def) ...))
         (begin (define-term name def)
                (unless (τ? (term name))
                  (error 'define-type-abbreviations "~a is not a type" 'def)))
         ...))

;; Numeric type abbrevs
(define-type-abbreviations
  #:abbrev-table type-abbrev-names
  (PosByte (Or One ByteLargerThanOne))
  (Byte (Or Zero PosByte))
  (PosIndex (Or One (Or ByteLargerThanOne PosIndexNotByte)))
  (Index (Or Zero PosIndex))
  (PosFixnum (Or PosFixnumNotIndex PosIndex))
  (NonnegFixnum (Or PosFixnum Zero))
  (NonposFixnum (Or NegFixnum Zero))
  (Fixnum (Or NegFixnum (Or Zero PosFixnum)))
  (PosInteger (Or PosIntegerNotFixnum PosFixnum))
  (NonnegInteger (Or Zero PosInteger))
  (NegInteger (Or NegFixnum NegIntegerNotFixnum))
  (NonposInteger (Or NegInteger Zero))
  ;; other types used in op types
  (PosIntegerNotByte (And PosInteger (Not Byte)))
  (PosIntegerNotIndex (And PosInteger (Not Index)))
  (Integer (Or NegInteger (Or Zero PosInteger)))
  (PosRational (Or PosRationalNotInteger PosInteger))
  (NonnegRational (Or Zero PosRational))
  (NegRational (Or NegRationalNotInteger NegInteger))
  (NonposRational (Or NegRational Zero))
  (Rational (Or NegRational (Or Zero PosRational)))
  (FloatZero (Or FloatPosZero (Or FloatNegZero FloatNaN)))
  (PosFloat (Or PosFloatNumber (Or PosFloatInfinity FloatNaN)))
  (NonnegFloat (Or PosFloat FloatZero))
  (NegFloat (Or NegFloatNumber (Or NegFloatInfinity FloatNaN)))
  (NonposFloat (Or NegFloat FloatZero))
  (Float (Or NegFloat (Or FloatZero PosFloat)))
  (SomeNaN (Or SingleFloatNaN FloatNaN))
  (SingleFloatZero (Or SingleFloatPosZero (Or SingleFloatNegZero SingleFloatNaN)))
  (InexactRealNaN (Or FloatNaN SingleFloatNaN))
  (InexactRealPosZero (Or SingleFloatPosZero FloatPosZero))
  (InexactRealNegZero (Or SingleFloatNegZero FloatNegZero))
  (InexactRealZero (Or InexactRealPosZero (Or InexactRealNegZero InexactRealNaN)))
  (PosSingleFloat (Or PosSingleFloatNumber (Or PosSingleFloatInfinity SingleFloatNaN)))
  (PosInexactReal (Or PosSingleFloat PosFloat))
  (NonnegSingleFloat (Or PosSingleFloat SingleFloatZero))
  (NonnegInexactReal (Or PosInexactReal InexactRealZero))
  (NegSingleFloat (Or NegSingleFloatNumber (Or NegSingleFloatInfinity SingleFloatNaN)))
  (NegInexactReal (Or NegSingleFloat NegFloat))
  (NonposSingleFloat (Or NegSingleFloat SingleFloatZero))
  (NonposInexactReal (Or NegInexactReal InexactRealZero))
  (SingleFloat (Or NegSingleFloat (Or SingleFloatZero PosSingleFloat)))
  (InexactReal (Or SingleFloat Float))
  (PosInfinity (Or PosFloatInfinity PosSingleFloatInfinity))
  (NegInfinity (Or NegFloatInfinity NegSingleFloatInfinity))
  (RealZero (Or Zero InexactRealZero))
  (PosReal (Or PosRational PosInexactReal))
  (NonnegReal (Or NonnegRational NonnegInexactReal))
  (NegReal (Or NegRational NegInexactReal))
  (NonposReal (Or NonposRational NonposInexactReal))
  ;; Real types w/ NaN excluded (useful for comparison ops, etc)
  (RealZeroNoNaN (And RealZero (Not SomeNaN)))
  (PosRealNoNaN (And PosReal (Not SomeNaN)))
  (NonnegRealNoNaN (And NonnegReal (Not SomeNaN)))
  (NegRealNoNaN (And NegReal (Not SomeNaN)))
  (NonposRealNoNaN (And NonposReal (Not SomeNaN)))
  (Real (Or Rational InexactReal))
  (RealNoNaN (And Real (Not SomeNaN)))
  (ExactNumber (Or ExactImaginary (Or ExactComplex Rational)))
  (InexactImaginary (Or FloatImaginary SingleFloatImaginary))
  (Imaginary (Or ExactImaginary InexactImaginary))
  (InexactComplex (Or FloatComplex SingleFloatComplex))
  (Number (Or Real (Or Imaginary (Or ExactComplex InexactComplex))))
  )




