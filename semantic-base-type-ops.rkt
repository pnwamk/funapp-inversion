#lang typed/racket/base

(require racket/unsafe/ops
         racket/match
         "semantic-type-rep.rkt")

(provide base-and base-or base-diff
         top-BASE bot-BASE)

(define-type NUMERIC-BASE
  [U 'Zero
     'One
     'Byte-Larger-Than-One
     'Positive-Index-Not-Byte
     'Positive-Fixnum-Not-Index
     'Negative-Fixnum
     'Positive-Integer-Not-Fixnum
     'Negative-Integer-Not-Fixnum
     'Positive-Rational-Not-Integer
     'Negative-Rational-Not-Integer
     'Float-NaN
     'Float-Positive-Zero
     'Float-Negative-Zero
     'Positive-Float-Number
     'Positive-Float-Infinity
     'Negative-Float-Number
     'Negative-Float-Infinity
     'Single-Float-NaN
     'Single-Float-Positive-Zero
     'Single-Float-Negative-Zero
     'Positive-Single-Float-Number
     'Positive-Single-Float-Infinity
     'Negative-Single-Float-Number
     'Negative-Single-Float-Infinity
     'Exact-Imaginary
     'Exact-Complex
     'Float-Imaginary
     'Single-Float-Imaginary
     'Float-Complex
     'Single-Float-Complex])

(: base-list (Listof NUMERIC-BASE))
(define base-list
  '[Zero
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
    Single-Float-Complex])

(: base-bit-table (HT NUMERIC-BASE Fixnum))
(define base-bit-table
  (for/hash : (HT NUMERIC-BASE Fixnum)
    ([sym : NUMERIC-BASE(in-list base-list)]
     [n : Natural (in-naturals 1)])
    (values sym (assert (arithmetic-shift #b1 n) fixnum?))))

(: symbols->BASE (-> (Listof NUMERIC-BASE) BASE))
(define (symbols->BASE syms)
  (base
   #t
   (foldl (λ ([sym : NUMERIC-BASE]
              [acc : Fixnum])
            (hash-ref base-bit-table sym))
          #b0
          syms)))

(define-syntax-rule (SIGN-MASK)
  #b1111111111111111111111111111110)
(define-syntax-rule (BIT-MASK)
  #b0000000000000000000000000000001)

(void
 (assert (SIGN-MASK) fixnum?)
 (assert (BIT-MASK) fixnum?))


(unless (eqv? (unsafe-fxior (SIGN-MASK) (BIT-MASK))
              (sub1 (arithmetic-shift 1 (add1 (length base-list)))))
  (error "masks and base-list out of sync"))

(: base-sign (-> BASE Boolean))
(define (base-sign b)
  (unsafe-fx= 0 (unsafe-fxand (BASE-data b) (SIGN-MASK))))

(: base-bits (-> BASE Fixnum))
(define (base-bits b)
  (unsafe-fxand (BASE-data b) (BIT-MASK)))

(: base (-> Boolean Fixnum BASE))
(define (base sign bits)
  (cond
    [sign (make-BASE (unsafe-fxior bits (SIGN-MASK)))]
    [else (make-BASE bits)]))

(define-syntax-rule (unsafe-fxdiff bits1 bits2)
  (unsafe-fxand bits1 (unsafe-fxnot bits2)))

(: base-or (-> BASE BASE BASE))
(define (base-or b1 b2)
  (define bits1 (base-bits b1))
  (define bits2 (base-bits b2))
  (match* ((base-sign b1) (base-sign b2))
    [(#t #t) (base #t (unsafe-fxior  bits1 bits2))]
    [(#t #f) (base #f (unsafe-fxdiff bits1 bits2))]
    [(#f #t) (base #f (unsafe-fxdiff bits2 bits1))]
    [(#f #f) (base #f (unsafe-fxand  bits1 bits2))]))

(: base-and (-> BASE BASE BASE))
(define (base-and b1 b2)
  (define bits1 (base-bits b1))
  (define bits2 (base-bits b2))
  (match* ((base-sign b1) (base-sign b2))
    [(#t #t) (base #t (unsafe-fxand  bits1 bits2))]
    [(#t #f) (base #t (unsafe-fxdiff bits1 bits2))]
    [(#f #t) (base #t (unsafe-fxdiff bits2 bits1))]
    [(#f #f) (base #f (unsafe-fxior  bits1 bits2))]))

(: base-diff (-> BASE BASE BASE))
(define (base-diff b1 b2)
  (define bits1 (base-bits b1))
  (define bits2 (base-bits b2))
  (match* ((base-sign b1) (base-sign b2))
    [(#t #t) (base #t (unsafe-fxdiff bits1 bits2))]
    [(#t #f) (base #t (unsafe-fxand  bits1 bits2))]
    [(#f #t) (base #t (unsafe-fxior  bits2 bits1))]
    [(#f #f) (base #t (unsafe-fxior  bits2 bits1))]))

(define top-BASE (base #f #b0))
(define bot-BASE (base #t #b0))
