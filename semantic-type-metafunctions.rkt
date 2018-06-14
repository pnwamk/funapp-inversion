#lang typed/racket/base

(require racket/match
         "semantic-type-rep.rkt"
         "semantic-type-ops.rkt")

(provide project
         domain
         funapp)

(: project (-> (U 1 2) TYPE (U TYPE False)))
(define (project i t)
  (cond
    [(not (subtype? t Any-Prod-TYPE)) #false]
    [else
     (let loop : TYPE
       ([bdd : BDD (TYPE-prods t)]
        [s1 : TYPE Any-TYPE]
        [s2 : TYPE Any-TYPE]
        [N : (Listof ATOM) '()])
       (match bdd
         ['BOT Empty-TYPE]
         [_ #:when (or (empty? s1) (empty? s2)) Empty-TYPE]
         ['TOP (prod-phi i s1 s2 N)]
         [(NODE (and a (cons t1 t2)) l m r)
          (define tl (loop l (type-and s1 t1) (type-and s2 t2) N))
          (define tm (loop m s1 s2 N))
          (define tr (loop r s1 s2 (cons a N)))
          (type-or tl (type-or tm tr))]))]))

(: prod-phi (-> (U 1 2) TYPE TYPE (Listof ATOM) TYPE))
(define (prod-phi i s1 s2 N)
  (match N
    [_ #:when (or (empty? s1) (empty? s2)) Empty-TYPE]
    [(list) (if (eqv? i 1) s1 s2)]
    [(cons (cons t1 t2) N)
     (type-or (prod-phi i (type-diff s1 t1) s2 N)
              (prod-phi i s1 (type-diff s2 t2) N))]))

(: domain (-> TYPE (U TYPE False)))
(define (domain t)
  (cond
    [(not (subtype? t Any-Arrow-TYPE)) #false]
    [else
     (let loop : TYPE
       ([bdd : BDD (TYPE-arrows t)]
        [t : TYPE Empty-TYPE])
       (match bdd
         ['TOP t]
         ['BOT Any-TYPE]
         [(NODE (cons s1 _) l m r)
          (type-and (loop l (type-or t s1))
                    (type-and (loop m t)
                              (loop r t)))]))]))


(: funapp (-> TYPE TYPE (U TYPE False)))
(define (funapp fun arg)
  (define dom (domain fun))
  (cond
    [(or (not dom) (not (subtype? arg dom))) #false]
    [else
     (let loop : TYPE
       ([bdd (TYPE-arrows fun)]
        [arg : TYPE arg]
        [res : TYPE Any-TYPE])
       (match bdd
         ['BOT Empty-TYPE]
         [_ #:when (empty? arg) Empty-TYPE]
         ['TOP res]
         [(NODE (cons s1 s2) l m r)
          (define tl1 (loop l arg (type-and res s2)))
          (define tl2 (loop l (type-diff arg s1) res))
          (define tm (loop m arg res))
          (define tr (loop r arg res))
          (type-or tl1 (type-or tl2 (type-or tm tr)))]))]))