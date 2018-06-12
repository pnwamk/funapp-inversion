#lang racket/base

(require redex/reduction-semantics
         racket/match
         racket/list)

(provide (all-defined-out))


(define-language base
  ;; numeric type primitives
  [nbase ::=
         Zero
         One
         Byte-Larger-Than-One
         Positive-Index-Not-Byte
         Positive-Fixnum-Not-Index
         Negative-Fixnum
         Positive-Integer-Not-Fixnum
         Negative-Integer-Not-Fixnum
         Positive-Rational-Not-Integer
         Negative-Rational-Not-Integer
         Float-NaN
         Float-Positive-Zero
         Float-Negative-Zero
         Positive-Float-Number
         Positive-Float-Infinity
         Negative-Float-Number
         Negative-Float-Infinity
         Single-Float-NaN
         Single-Float-Positive-Zero
         Single-Float-Negative-Zero
         Positive-Single-Float-Number
         Positive-Single-Float-Infinity
         Negative-Single-Float-Number
         Negative-Single-Float-Infinity
         Exact-Imaginary
         Exact-Complex
         Float-Imaginary
         Single-Float-Imaginary
         Float-Complex
         Single-Float-Complex]
  ;; values, primitive numeric ops, numeric expressions
  [val ::= number]
  [uop ::= add1]
  [bop ::= +]
  [comp ::= <]
  [pred ::= number? positive?]
  [nexp ::= val (uop nexp) (bop nexp nexp)]
  [bexp ::= (pred nexp) (comp nexp nexp)]
  [operator ::= pred comp uop bop]
  ;; syntactic types
  [ntype ::= nbase (U nbase ...)]
  [btype ::= True False (U True False) (U False True)]
  [type ::= ntype btype Any]
  [prop ::= tt ff (∈ 0 type) (∉ 0 type) (∈ 1 type) (∉ 1 type) (∧ (∈ 0 type) (∈ 1 type))]
  [domain ::= (type type ...)]
  [range ::= (type) (type prop prop)]
  [arrow ::= (-> domain range)]
  [funtype ::= (case-> arrow arrow ...)]
  [syntactic-type ::= funtype type]
  ;; semantic types
  [ι ::= nbase True False]
  [τ ::= ι (Pair τ τ) (Fun τ τ)
     (Or τ τ) (And τ τ) (Not τ)
     Any Empty])

(define-term Boolean (U True False))

(define operator? (redex-match? base operator))

(define-metafunction base
  union : ntype ... -> ntype
  [(union nbase ...)
   ,(match (remove-duplicates (term (nbase ...)))
      [(list t) t]
      [ts (cons 'U ts)])]
  [(union any_0 ... (U nbase ...) any_1 ...)
   (union any_0 ... nbase ... any_1 ...)])

(define ntype? (redex-match? base ntype))
(define funtype? (redex-match? base funtype))
(define arrow? (redex-match? base arrow))

(define-syntax-rule (define-syntactic-numeric-unions
                      table-name
                      [name (content contents ...)] ...)
  (begin
    (define-term name (union content contents ...))
    ...
    (unless (ntype? (term name))
      (error 'define-syntactic-numeric-unions "invalid ntype ~a" (term name)))
    ...
    (define table-name (make-immutable-hash (list (cons 'name (term name)) ...)))))

(define-syntactic-numeric-unions
  numeric-unions-table
  [Positive-Byte (One Byte-Larger-Than-One)]
  [Byte (Zero Positive-Byte)]
  
  [Positive-Index (One Byte-Larger-Than-One Positive-Index-Not-Byte)]
  [Index (Zero Positive-Index)]
  
  [Positive-Fixnum (Positive-Fixnum-Not-Index Positive-Index)]
  [Nonnegative-Fixnum (Positive-Fixnum Zero)]
  
  [Nonpositive-Fixnum (Negative-Fixnum Zero)]
  [Fixnum (Negative-Fixnum Zero Positive-Fixnum)]

  [Positive-Integer (Positive-Integer-Not-Fixnum Positive-Fixnum)]
  [Nonnegative-Integer (Zero Positive-Integer)]

  [Negative-Integer (Negative-Fixnum Negative-Integer-Not-Fixnum)]
  [Nonpositive-Integer (Negative-Integer Zero)]
  [Integer (Negative-Integer Zero Positive-Integer)]

  [Positive-Rational (Positive-Rational-Not-Integer Positive-Integer)]
  [Nonnegative-Rational (Zero Positive-Rational)]

  [Negative-Rational (Negative-Rational-Not-Integer Negative-Integer)]
  [Nonpositive-Rational (Negative-Rational Zero)]
  [Rational (Negative-Rational Zero Positive-Rational)]

  [Float-Zero (Float-Positive-Zero Float-Negative-Zero Float-NaN)]
  [Positive-Float (Positive-Float-Number Positive-Float-Infinity Float-NaN)]
  [Nonnegative-Float (Positive-Float Float-Zero)]
  [Negative-Float (Negative-Float-Number Negative-Float-Infinity Float-NaN)]
  [Nonpositive-Float (Negative-Float Float-Zero)]
  [Float (Negative-Float-Number Negative-Float-Infinity Float-Negative-Zero
                                Float-Positive-Zero
                                Positive-Float-Number Positive-Float-Infinity Float-NaN)]

  [Single-Float-Zero (Single-Float-Positive-Zero Single-Float-Negative-Zero Single-Float-NaN)]

  [Inexact-Real-NaN (Float-NaN Single-Float-NaN)]
  [Inexact-Real-Positive-Zero (Single-Float-Positive-Zero Float-Positive-Zero)]
  [Inexact-Real-Negative-Zero (Single-Float-Negative-Zero Float-Negative-Zero)]
  [Inexact-Real-Zero (Inexact-Real-Positive-Zero
                      Inexact-Real-Negative-Zero
                      Inexact-Real-NaN)]

  [Positive-Single-Float (Positive-Single-Float-Number Positive-Single-Float-Infinity Single-Float-NaN)]
  [Positive-Inexact-Real (Positive-Single-Float Positive-Float)]
  [Nonnegative-Single-Float (Positive-Single-Float Single-Float-Zero)]
  [Nonnegative-Inexact-Real (Positive-Inexact-Real Inexact-Real-Zero)]
  [Negative-Single-Float (Negative-Single-Float-Number Negative-Single-Float-Infinity Single-Float-NaN)]
  [Negative-Inexact-Real (Negative-Single-Float Negative-Float)]
  [Nonpositive-Single-Float (Negative-Single-Float Single-Float-Zero)]
  [Nonpositive-Inexact-Real (Negative-Inexact-Real Inexact-Real-Zero)]
  [Single-Float (Negative-Single-Float
                 Single-Float-Negative-Zero
                 Single-Float-Positive-Zero
                 Positive-Single-Float
                 Single-Float-NaN)]
  [Inexact-Real (Single-Float Float)]
  [Positive-Infinity (Positive-Float-Infinity Positive-Single-Float-Infinity)]
  [Negative-Infinity (Negative-Float-Infinity Negative-Single-Float-Infinity)]

  [Real-Zero (Zero Inexact-Real-Zero)]
  [Real-Zero-No-NaN (Zero Inexact-Real-Positive-Zero Inexact-Real-Negative-Zero)]
  [Positive-Real (Positive-Rational Positive-Inexact-Real)]
  [Nonnegative-Real (Nonnegative-Rational Nonnegative-Inexact-Real)]
  [Negative-Real (Negative-Rational Negative-Inexact-Real)]
  [Nonpositive-Real (Nonpositive-Rational Nonpositive-Inexact-Real)]
  [Real (Rational Inexact-Real)]

  [Exact-Number (Exact-Imaginary Exact-Complex Rational)]
  [Inexact-Imaginary (Float-Imaginary Single-Float-Imaginary)]
  [Imaginary (Exact-Imaginary Inexact-Imaginary)]
  [Inexact-Complex (Float-Complex Single-Float-Complex)]
  [Number (Real Imaginary Exact-Complex Inexact-Complex)])



(define (index? x) (and (fixnum? x) (>= x 0) (fixnum? (* x 4))))

(define (exact-rational? x) (and (rational? x) (exact? x)))

(define nbase-type-predicate-table
  (hash
   'Zero (λ (n) (eq? n 0))
   'One (λ (n) (eq? n 1))
   'Byte-Larger-Than-One (λ (n) (and (byte? n) (> n 1)))
   'Positive-Index-Not-Byte (λ (x) (and (index? x)
                                        (positive? x)
                                        (not (byte? x))))
   'Positive-Fixnum-Not-Index (λ (x) (and (fixnum? x)
                                          (positive? x)
                                          (not (index? x))))
   'Negative-Fixnum (λ (x) (and (fixnum? x)
                                (negative? x)))
   'Positive-Integer-Not-Fixnum (λ (x) (and (exact-integer? x)
                                            (positive? x)
                                            (not (fixnum? x))))
   'Negative-Integer-Not-Fixnum (λ (x) (and (exact-integer? x)
                                            (negative? x)
                                            (not (fixnum? x))))
   'Positive-Rational-Not-Integer (λ (x) (and (exact-rational? x)
                                              (positive? x)
                                              (not (exact-integer? x))))
   'Negative-Rational-Not-Integer (λ (x) (and (exact-rational? x)
                                              (negative? x)
                                              (not (exact-integer? x))))
   'Float-NaN (λ (x) (and (flonum? x) (eqv? x +nan.0)))
   'Float-Positive-Zero (λ (x) (eqv? x 0.0))
   'Float-Negative-Zero (λ (x) (eqv? x -0.0))
   'Positive-Float-Number (λ (x) (and (flonum? x) (positive? x) (not (eqv? x +inf.0))))
   'Positive-Float-Infinity (λ (x) (eqv? x +inf.0))
   'Negative-Float-Number (λ (x) (and (flonum? x) (negative? x) (not (eqv? x -inf.0))))
   'Negative-Float-Infinity (λ (x) (eqv? x -inf.0))
   'Single-Float-NaN (λ (x) (and (single-flonum? x) (eqv? x +nan.f)))
   'Single-Float-Positive-Zero (λ (x) (eqv? x 0.0f0))
   'Single-Float-Negative-Zero (λ (x) (eqv? x -0.0f0))
   'Positive-Single-Float-Number (λ (x) (and (single-flonum? x) (positive? x) (not (eqv? x +inf.f))))
   'Positive-Single-Float-Infinity (λ (x) (eqv? x +inf.f))
   'Negative-Single-Float-Number (λ (x) (and (single-flonum? x) (negative? x) (not (eqv? x -inf.f))))
   'Negative-Single-Float-Infinity (λ (x) (eqv? x -inf.f))
   'Exact-Imaginary (λ (x) (and (number? x)
                                (not (real? x))
                                (eqv? 0 (real-part x))
                                (exact? (imag-part x))))
   'Exact-Complex (λ (x) (and (number? x)
                              (not (real? x))
                              (not (eqv? 0 (real-part x)))
                              (exact? (real-part x))
                              (exact? (imag-part x))))
   'Float-Imaginary (λ (x)
                      (and (number? x)
                           (flonum? (imag-part x))
                           (eqv? 0 (real-part x))))
   'Single-Float-Imaginary (λ (x)
                             (and (number? x)
                                  (single-flonum? (imag-part x))
                                  (eqv? 0 (real-part x))))
   'Float-Complex (λ (x)
                    (and (number? x)
                         (flonum? (imag-part x))
                         (flonum? (real-part x))))
   'Single-Float-Complex (λ (x)
                           (and (number? x)
                                (single-flonum? (imag-part x))
                                (single-flonum? (real-part x))))))

(define (nbase->pred nt)
  (hash-ref nbase-type-predicate-table nt
            (λ () (error 'nbase->pred "~v is not a known numeric base type" nt))))

(define nbase-predicate-type-table
  (for/list ([(ty pred) (in-hash nbase-type-predicate-table)])
    (cons pred ty)))


(define (number->ntype n)
  (or (for/or ([pred/name (in-list nbase-predicate-type-table)])
        (and ((car pred/name) n) (cdr pred/name)))
      (error 'number->ntype "unable to determine type for ~v" n)))

(define-metafunction base
  syntactic->semantic : syntactic-type -> τ
  [(syntactic->semantic ι) ι]
  [(syntactic->semantic Any) Any]
  [(syntactic->semantic (U)) Empty]
  [(syntactic->semantic (U type_0 type_1 ...))
   ,(foldl (λ (elem acc) (term (Or ,elem ,acc)))
           (term type_0)
           (term (type_1 ...)))]
  [(syntactic->semantic (case-> (-> (type_d0) (type_r0))
                                (-> (type_d1) (type_r1))
                                ...))
   ,(foldl (λ (d r acc)
             (term (And (Fun (syntactic->semantic ,d)
                             (syntactic->semantic ,r))
                        ,acc)))
           (term (Fun (syntactic->semantic type_d0)
                      (syntactic->semantic type_r0)))
           (term (type_d1 ...))
           (term (type_r1 ...)))]
  [(syntactic->semantic (case-> (-> (type_d00 type_d01) (type_r0))
                                (-> (type_d10 type_d11) (type_r1))
                                ...))
   ,(foldl (λ (d0 d1 r acc)
             (term (And (Fun (Pair (syntactic->semantic ,d0)
                                   (syntactic->semantic ,d1))
                             (syntactic->semantic ,r))
                        ,acc)))
           (term (Fun (Pair (syntactic->semantic type_d00)
                            (syntactic->semantic type_d01))
                      (syntactic->semantic type_r0)))
           (term (type_d10 ...))
           (term (type_d11 ...))
           (term (type_r1 ...)))])
