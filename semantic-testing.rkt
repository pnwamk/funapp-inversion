#lang typed/racket/base

(require (for-syntax racket/base)
         "syntactic-type-rep.rkt"
         "semantic-type-rep.rkt"
         "semantic-type-ops.rkt"
         "conversion.rkt"
         "mtest.rkt")

(define-syntax (check<:-true stx)
  (syntax-case stx ()
    [(_ t1 t2)
     (quasisyntax/loc stx
       (chk #,(syntax/loc stx
                (subtype? (->semantic t1) (->semantic t2)))))]))

(define-syntax (check<:-false stx)
  (syntax-case stx ()
    [(_ t1 t2)
     (quasisyntax/loc stx
       (chk~ #,(syntax/loc stx
                 (subtype? (->semantic t1) (->semantic t2)))))]))


;; basic numeric subtyping
(check<:-true  Zero Number)
(check<:-false Number Zero)
(check<:-true  Byte Number)
(check<:-false Number Byte)

;; basic pair subtyping
(check<:-true  (PAIR Zero Zero) (PAIR Number Number))
(check<:-true  (PAIR Number Zero) (PAIR Number Number))
(check<:-true  (PAIR Zero Number) (PAIR Number Number))
(check<:-true  (PAIR Number Number) (PAIR Number Number))
(check<:-false  (PAIR Number Number) (PAIR Zero Zero))
(check<:-false  (PAIR Number Number) (PAIR Number Zero) )
(check<:-false  (PAIR Number Number) (PAIR Zero Number))