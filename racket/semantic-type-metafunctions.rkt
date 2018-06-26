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
         [(== bot eq?) Empty-TYPE]
         [(== top eq?) (prod-phi i s1 s2 N)]
         [(NODE: (and a (cons t1 t2)) l m r)
          (define s1* (type-and s1 t1))
          (define s2* (type-and s2 t2))
          (define tl (if (or (empty? s1*) (empty? s2*))
                         Empty-TYPE
                         (loop l s1* s2* N)))
          (define tm (loop m s1 s2 N))
          (define tr (loop r s1 s2 (cons a N)))
          (type-or tl (type-or tm tr))]))]))

(: prod-phi (-> (U 1 2) TYPE TYPE (Listof ATOM) TYPE))
(define (prod-phi i s1 s2 N)
  (match N
    [(list) (if (eqv? i 1) s1 s2)]
    [(cons (cons t1 t2) N)
     (define s1* (type-diff s1 t1))
     (define s2* (type-diff s2 t2))
     (type-or (if (empty? s1*) Empty-TYPE (prod-phi i s1* s2 N))
              (if (empty? s2*) Empty-TYPE (prod-phi i s1 s2* N)))]))

(: domain (-> TYPE (U TYPE False)))
(define (domain t)
  (cond
    [(not (subtype? t Any-Arrow-TYPE)) #false]
    [else
     (let loop : TYPE
       ([bdd : BDD (TYPE-arrows t)]
        [t : TYPE Empty-TYPE])
       (match bdd
         [(== top eq?) t]
         [(== bot eq?) Any-TYPE]
         [(NODE: (cons s1 _) l m r)
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
         [(== bot eq?) Empty-TYPE]
         [(== top eq?) (funapp-helper arg Any-TYPE P)]
         [(NODE: (and a (cons s1 _)) l m r)
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
    [(cons (cons s1 s2) P)
     (define res1 (let ([res* (type-and res s2)])
                    (if (empty? res*)
                        Empty-TYPE
                        (funapp-helper arg res* P))))
     (define res2 (let ([arg* (type-diff arg s1)])
                    (if (empty? arg*)
                        Empty-TYPE
                        (funapp-helper arg* res P))))
     (type-or res1 res2)]
    [_ res]))
