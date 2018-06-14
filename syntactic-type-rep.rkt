#lang typed/racket/base

(require racket/match
         racket/list
         racket/set)

(provide (except-out (all-defined-out)
                     define-numeric-base-types
                     define-numeric-base-types
                     define-syntactic-numeric-unions))

(define-syntax-rule (define-numeric-base-types
                      type-name
                      list-name
                      [base ...])
  (begin
    (begin
      (: base (quote base))
      (define base (quote base))) ...
    (define-type type-name (U (quote base) ...))
    (: list-name (Listof type-name))
    (define list-name (list (quote base) ...))))



(define-numeric-base-types
  NUMERIC-BASE
  numeric-base-list
  [Zero
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



(define-type NUMERIC (U NUMERIC-BASE (Pair 'U (Listof NUMERIC-BASE))))
(define-type BOOL (U 'TRUE 'FALSE 'BOOL))
(struct UNOP ([domain : NUMERIC]
              [codomain : NUMERIC])
  #:transparent)
(struct BINOP ([domain1 : NUMERIC]
               [domain2 : NUMERIC]
               [codomain : NUMERIC])
  #:transparent)
(struct COMP ([domain1 : NUMERIC]
              [domain2 : NUMERIC]
              [true-prop : PROP]
              [false-prop : PROP])
  #:transparent)

(struct PROP () #:transparent)
(struct TT PROP () #:transparent)
(struct FF PROP () #:transparent)
(struct ∈ PROP ([arg : (U 0 1)] [type : NUMERIC]) #:transparent)
(struct ∉ PROP ([arg : (U 0 1)] [type : NUMERIC]) #:transparent)
(struct ∧ PROP ([lhs : (U ∈ ∉)] [rhs : (U ∈ ∉)]) #:transparent)

(define tt (TT))
(define ff (FF))


(: union (-> NUMERIC NUMERIC NUMERIC))
(define (union n1 n2)
  (match* (n1 n2)
    [(n n) n]
    [((? symbol? n1) (? symbol? n2)) (list 'U n1 n2)]
    [((cons 'U types1) (? symbol? n2))
     (if (member n2 types1)
         n1
         (list* 'U n2 types1))]
    [((? symbol? n1) (cons 'U types2))
     (if (member n1 types2)
         n2
         (list* 'U n1 types2))]
    [((cons 'U types1) (cons 'U types2))
     (cons 'U (remove-duplicates (append types1 types2)))]))

(: Un (->* () () #:rest NUMERIC NUMERIC))
(define (Un . types)
  (foldl union '(U) types))

(define-syntax-rule (define-syntactic-numeric-unions
                      table-name
                      [name (content contents ...)] ...)
  (begin
    (begin
      (: name NUMERIC)
      (define name (Un content contents ...)))
    ...
    (define table-name
      (make-immutable-hash
       (list (cons (quote name) name) ...)))))

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

(: numeric-subtype? (-> NUMERIC NUMERIC Boolean))
(define (numeric-subtype? n1 n2)
  (match* (n1 n2)
    [((? symbol? n1) (? symbol? n2))
     (eq? n1 n2)]
    [((? symbol? n1) (cons 'U types))
     (and (member n1 types) #t)]
    [((cons 'U types) (? symbol? n2))
     (andmap (λ ([n1 : NUMERIC]) (numeric-subtype? n1 n2)) types)]
    [((cons 'U types1) (cons 'U types2))
     (subset? (list->set types1) (list->set types2))]))


(: syntactic-funapp (case->
                     [-> (Listof UNOP) NUMERIC (U NUMERIC False)]
                     [-> (Listof BINOP) NUMERIC NUMERIC (U NUMERIC False)]))
(define syntactic-funapp
  (case-lambda
    [(unops arg)
     (let loop ([unops : (Listof UNOP) unops])
       (match unops
         [(cons (UNOP dom rng) remaining)
          (if (numeric-subtype? arg dom)
              rng
              (loop remaining))]
         [_ #f]))]
    [(binops arg1 arg2)
     (let loop ([binops : (Listof BINOP) binops])
       (match binops
         [(cons (BINOP dom1 dom2 rng) remaining)
          (if (and (numeric-subtype? arg1 dom1)
                   (numeric-subtype? arg2 dom2))
              rng
              (loop remaining))]
         [_ #f]))]))
