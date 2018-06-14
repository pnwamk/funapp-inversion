#lang typed/racket/base

(require "semantic-type-rep.rkt"
         racket/match)

(provide subtype?
         empty?)


(: subtype? (-> TYPE TYPE Boolean))
(define (subtype? t1 t2)
  (empty? (type-diff t1 t2)))


(: empty? (-> TYPE Boolean))
(define empty?
  (let ([empty-table : (HT TYPE (U 'YES 'NO))
                     (make-weak-hasheq)])
    (λ (t)
      (cond
        [(eq? t Empty-TYPE) #t]
        [(or (not (eq? bot-BASE (TYPE-base t)))
             (eq? 'TOP (TYPE-prods t))
             (eq? 'TOP (TYPE-arrows t)))
         #f]
        [else
         (define cached-result (hash-ref empty-table t #f))
         (cond
           [(not cached-result)
            (match-define (TYPE b p a) t)
            (define result (and (empty-base? b)
                                (empty-prod? p)
                                (empty-arrow? a)))
            (hash-set! empty-table t (if result 'YES 'NO))
            result]
           [else (eq? cached-result 'YES)])]))))

(: empty-base? (-> BASE Boolean))
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
      ['BOT #true]
      ['TOP (or (empty? s1)
                (empty? s2)
                (prod-theta s1 s2 N))]
      [(NODE (and a (cons t1 t2)) l m r)
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
      [('BOT _) #true]
      [('TOP _) #false]
      [('TOP (cons (cons t1 t2) N))
       (or (and (subtype? t1 s) (arrow-theta t1 (type-not t2) P))
           (loop 'TOP s P N))]
      [((NODE (and a (cons s1 _)) l m r) _)
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

