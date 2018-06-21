#lang typed/racket/base

(require "semantic-type-rep.rkt"
         racket/match)

(provide subtype?
         empty?
         overlap?)


(: subtype? (-> TYPE TYPE Boolean))
(define (subtype? t1 t2)
  (empty? (type-diff t1 t2)))

(: overlap? (-> TYPE TYPE Boolean))
(define (overlap? t1 t2)
  (not (empty? (type-and t1 t2))))


(define empty-table : (HT Fixnum (Listof (Pair TYPE Boolean)))
  (make-hasheq))


(: empty? (-> TYPE Boolean))
(define (empty? t)
  (match-define (TYPE: b p a) t)
  (and (empty-base? b)
       (empty-prod? p)
       (empty-arrow? a)))

(: empty-base? (-> Fixnum Boolean))
(define (empty-base? b)
  (eq? b bot-BASE))

(: empty-prod? (-> BDD Boolean))
(define (empty-prod? bdd)
  (let loop : Boolean
    ([bdd : BDD bdd]
     [s1 : TYPE Any-TYPE]
     [s2 : TYPE Any-TYPE]
     [N : (Listof ATOM) '()])
    (match bdd
      [(== bot eq?) #true]
      [(== top eq?)
       (or (empty? s1)
           (empty? s2)
           (prod-theta s1 s2 N))]
      [(NODE: (and a (cons t1 t2)) l m r)
       (and (loop l (type-and s1 t1) (type-and s2 t2) N)
            (loop m s1 s2 N)
            (loop r s1 s2 (cons a N)))])))

(: prod-theta (-> TYPE TYPE (Listof ATOM) Boolean))
(define (prod-theta s1 s2 N)
  (match N
    [(cons (cons t1 t2) N)
     (define s1* (type-diff s1 t1))
     (and (let ([s1* (type-diff s1 t1)])
            (or (empty? s1*) (prod-theta s1* s2 N)))
          (let ([s2* (type-diff s2 t2)])
            (or (empty? s2*) (prod-theta s1 s2* N))))]
    [_ #false]))

(: empty-arrow? (-> BDD Boolean))
(define (empty-arrow? bdd)
  (let loop : Boolean
    ([bdd : BDD bdd]
     [s : TYPE Empty-TYPE]
     [P : (Listof ATOM) '()]
     [N : (Listof ATOM) '()])
    (match* (bdd N)
      [((== bot eq?) _) #true]
      [((== top eq?) _) #false]
      [((== top eq?) (cons (cons t1 t2) N))
       (or (and (subtype? t1 s) (arrow-theta t1 (type-not t2) P))
           (loop top s P N))]
      [((NODE: (and a (cons s1 _)) l m r) _)
       (and (loop l (type-or s s1) (cons a P) N)
            (loop m s P N)
            (loop r s P (cons a N)))])))


(: arrow-theta (-> TYPE TYPE (Listof ATOM) Boolean))
(define (arrow-theta t1 t2 P)
  (match P
    [(cons (cons s1 s2) P)
     (and (let ([t1* (type-diff t1 s1)])
            (or (empty? t1*) (arrow-theta t1* t2 P)))
          (let ([t2* (type-and t2 s2)])
            (or (empty? t2*) (arrow-theta t1 t2* P))))]
    [_ (or (empty? t1) (empty? t2))]))

