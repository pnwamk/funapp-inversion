#lang racket/base

(require redex/reduction-semantics
         "base-lang.rkt")

(provide semantic-funtype-table)

(define-syntax-rule (define-funtype-table funtype-table
                      [name (case-> case ...)]
                      ...)
  (begin
    (cond
      [(not (operator? (term name)))
       (error 'define-funtype-table "~a is not an operator" 'name)]
      [(not (arrow? (term case)))
       (error 'define-funtype-table "~a is not a valid arrow"
              'case)]
      ...)
    ...
    (define funtype-table
      (make-immutable-hash (list (cons (term name) (term (case-> case ...))) ...)))))

(define-funtype-table
  semantic-funtype-table
  [add1 (case-> ;; 23 cases --> 13 cases
         (-> (Zero) (One))
         (-> (One) (Byte))
         (-> (Byte) (Index))
         (-> (Index) (Fixnum))
         (-> (Integer) (Integer))
         (-> (Rational) (Rational))
         (-> (Float) (Float))
         (-> (Single-Float) (Single-Float))
         (-> (Float-Complex) (Float-Complex))
         (-> (Single-Float-Complex) (Single-Float-Complex))
         (-> (Nonnegative-Real) (Positive-Real))
         (-> (Negative-Fixnum) (Nonpositive-Fixnum))
         (-> (Negative-Integer) (Nonpositive-Integer)))])

         

;(define (<-type-pattern base pos non-neg neg non-pos [zero (term Real-Zero)]
;                        #:no-false-props? [no-false-props? #f])
;  (define (<-case l r true-prop false-prop)
;    (term (-> ,base ,zero Boolean : ,true-prop ,(if no-false-props? (term tt) false-prop))))
;  (list (<-case base zero (term (∈ 0 ,neg)) (term (∈ 0 ,non-neg)))
;        (<-case zero base (term (∈ 1 ,pos)) (term (∈ 1 ,non-pos)))
;        (<-case base (term Positive-Real) (term tt) (term (∈ 0 ,pos)))
;        (<-case base (term Nonnegative-Real) (term tt) (term (∈ 0 ,non-neg)))
;        (<-case (term Nonnegative-Real) base (term (∈ 1 ,pos)) 'tt)
;        (<-case base (term Nonpositive-Real) (term (∈ 0 ,neg)) 'tt)
;        (<-case (term Negative-Real) base (term tt) (term (∈ 1 ,neg)))
;        (<-case (term Nonpositive-Real) base (term tt) (term (∈ 1 ,non-pos)))))
;
;(<-type-pattern (term Integer)
;                (term Positive-Integer)
;                (term Nonnegative-Integer)
;                (term Negative-Integer)
;                (term Nonpositive-Integer)
;                (term Zero))
;(<-type-pattern (term Rational)
;                (term Positive-Rational)
;                (term Nonnegative-Rational)
;                (term Negative-Rational)
;                (term Nonpositive-Rational)
;                (term Zero))
;(<-type-pattern (term Float)
;                (term Positive-Float)
;                (term Nonnegative-Float)
;                (term Negative-Float)
;                (term Nonpositive-Float)
;                #:no-false-props? #t)
;(<-type-pattern (term Single-Float)
;                (term Positive-Single-Float)
;                (term Nonnegative-Single-Float)
;                (term Negative-Single-Float)
;                (term Nonpositive-Single-Float)
;                #:no-false-props? #t)
;(<-type-pattern (term Inexact-Real)
;                (term Positive-Inexact-Real)
;                (term Nonnegative-Inexact-Real)
;                (term Negative-Inexact-Real)
;                (term Nonpositive-Inexact-Real)
;                #:no-false-props? #t)
;(<-type-pattern (term Real)
;                (term Positive-Real)
;                (term Nonnegative-Real)
;                (term Negative-Real)
;                (term Nonpositive-Real)
;                #:no-false-props? #t)

