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
        [P : (Listof ATOM) '()])
       (match bdd
         ['BOT Empty-TYPE]
         ['TOP (funapp-helper arg Any-TYPE P)]
         [(NODE (and a (cons s1 _)) l m r)
          (define tl
            (cond
              [(overlap? s1 arg) (loop l (cons a P))]
              [else (loop l P)]))
          (define tm (loop m P))
          (define tr (loop r P))
          (type-or tl (type-or tm tr))]))]))

(: funapp-helper (-> TYPE TYPE (Listof ATOM) TYPE))
(define (funapp-helper arg res P)
  (match P
    [_ #:when (or (empty? arg) (empty? res)) Empty-TYPE]
    [(cons (cons s1 s2) P)
     (define res1 (funapp-helper arg (type-and res s2) P))
     (define res2 (funapp-helper (type-diff arg s1) res P))
     (type-or res1 res2)]
    [_ res]))
