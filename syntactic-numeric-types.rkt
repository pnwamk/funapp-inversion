#lang racket/base

(require redex/reduction-semantics
         "syntactic-lang.rkt")

(define-syntax-rule (define-funtype name body)
  (begin
    (define-term name body)
    (unless (funtype? (term name))
      (error 'define-funtype "~a is not a funtype" 'name))))

(define-funtype type-of-add1
  (case->
   (-> (Integer) (Integer))))

(define-funtype type-of-+
  (case->
   (-> (Integer Integer) (Integer))))

(define-funtype type-of-<
  (case->
   (-> (Integer Integer) (Bool tt tt))))
