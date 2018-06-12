#lang racket/base

(require "base-lang.rkt"
         "syntactic-numeric-types.rkt"
         "semantic-numeric-types.rkt"
         "semantic-subtyping/interface.rkt"
         redex/reduction-semantics
         racket/list)

(define add1-syntactic
  (term (syntactic->semantic
         ,(hash-ref syntactic-funtype-table 'add1))))
(define add1-semantic
  (term (syntactic->semantic
         ,(hash-ref semantic-funtype-table 'add1))))

(define numeric-base-types
  '(Zero
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
    Single-Float-Complex))

(for* ([ntypes (in-combinations numeric-base-types)]
       [raw-arg-type (in-value (cons 'U ntypes))]
       [arg-type (in-value (term (syntactic->semantic ,raw-arg-type)))])
  (define syntactic-result (maybe-apply-function add1-syntactic arg-type))
  (define semantic-result (maybe-apply-function add1-semantic arg-type))
  (cond
    [(not syntactic-result)
     (error 'add1-tests "syntactic apply failed, argument type: ~a\n" raw-arg-type)]
    [(not semantic-result)
     (error 'add1-tests "semantic apply failed, argument type: ~a\n" raw-arg-type)]
    [(not (semantic-subtype? semantic-result syntactic-result))
     (error 'add1-tests "semantic result not subtype of syntactic result!\n arg: ~a\n semantic: ~a\n syntactic: ~a\n"
            raw-arg-type
            semantic-result
            syntactic-result)]
    [else
     (test-equal #t #t)]))

(test-results)
