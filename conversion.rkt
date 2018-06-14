#lang typed/racket/base

(require racket/match
         "syntactic-type-rep.rkt"
         "semantic-type-rep.rkt")

(provide ->semantic)

(: ->semantic (-> (U NUMERIC UNOP BINOP (Listof UNOP) (Listof BINOP))
                  TYPE))
(define (->semantic t)
  (match t
    [(? symbol? s) (type (symbols->BASE (list s)) 'BOT 'BOT)]
    [(UNOP dom rng) (Arrow-TYPE (->semantic dom) (->semantic rng))]
    [(BINOP dom1 dom2 rng) (Arrow-TYPE (Prod-TYPE (->semantic dom1) (->semantic dom2))
                                       (->semantic rng))]
    [(cons 'U types) (type (symbols->BASE types) 'BOT 'BOT)]
    [(cons (? UNOP? u) unops)
     (foldl (λ ([u : UNOP]
                [t : TYPE])
              (type-and (->semantic u) t))
            (->semantic u)
            unops)]
    [(cons (? BINOP? b) binops)
     (foldl (λ ([u : BINOP]
                [t : TYPE])
              (type-and (->semantic u) t))
            (->semantic b)
            binops)]))

