#lang racket/base

(require "type-rep.rkt"
         "inhabitation.rkt"
         "metafunctions.rkt"
         redex/reduction-semantics)

(provide semantic-subtype?
         maybe-apply-function)

(define (semantic-subtype? t1 t2)
  (term (subtype (parse ,t1) (parse ,t2))))

(define (maybe-apply-function fun-type arg-type)
  (term (read-back (maybe-funapp (parse ,fun-type) (parse ,arg-type)))))
