#lang typed/racket/base

(require racket/match
         racket/unsafe/ops)

(provide (except-out (all-defined-out)
                     make-memo-entry
                     hash-construct))

(define-type (HT K V) (HashTable K V))

(define-syntax make-memo-entry
  (syntax-rules ()
    [(_ v) v]
    [(_ k v) (make-weak-hasheq (list ((ann cons (All (A B) (-> A B (Pair A B))))
                                      k v)))]
    [(_ k1 k2 . rest) (make-weak-hasheq
                       (list (cons k1 (make-memo-entry k2 . rest))))]))

(define-syntax hash-construct
  (syntax-rules ()
    [(_ cur make-expr) cur]
    [(_ cur make-expr field rest ...)
     (let ([next (hash-ref cur field #f)])
       (cond
         [next (hash-construct next make-expr rest ...)]
         [else
          (define val make-expr)
          (define entry (make-memo-entry rest ... val))
          (hash-set! cur field entry)
          val]))]))

(define-type ATOM (Pair TYPE TYPE))

(: atom (-> TYPE TYPE ATOM))
(define atom
  (let ([atom-table : (HT TYPE (HT TYPE (Pair TYPE TYPE)))
                    (make-weak-hasheq)])
    (λ (a d)
      (hash-construct atom-table (cons a d) a d))))

(struct NODE ([atom : ATOM]
              [left : BDD]
              [middle : BDD]
              [right : BDD]))

(: make-NODE (-> ATOM BDD BDD BDD
                 NODE))
(define make-NODE
  (let ([node-table : (HT ATOM (HT BDD (HT BDD (HT BDD NODE))))
                    (make-weak-hasheq)])
    (λ (a l m r)
      (hash-construct node-table (NODE a l m r) a l m r))))

(define top 'TOP)
(: top? (-> Any Boolean : TOP))
(define (top? x) (eq? x 'TOP))

(define bot 'TOP)
(: bot? (-> Any Boolean : BOT))
(define (bot? x) (eq? x 'BOT))

(define-type TOP 'TOP)
(define-type BOT 'BOT)
(define-type BDD (U TOP BOT NODE))


(struct BASE ([data : Fixnum]) #:transparent)

(: make-BASE (-> Fixnum BASE))
(define make-BASE
  (let ([base-table : (HT BASE BASE) (make-weak-hasheq)])
    (λ (data)
      (define b (BASE data))
      (cond
        [(hash-ref base-table b #f)]
        [else (hash-set! base-table b b)
              b]))))

(struct TYPE ([base : BASE] [prods : BDD] [arrows : BDD]))

(: type (-> BASE BDD BDD TYPE))
(define type
  (let ([type-table : (HT BASE (HT BDD (HT BDD TYPE)))
                    (make-weak-hasheq)])
    (λ (b p a)
      (hash-construct type-table (TYPE b p a) b p a))))

(define-syntax lexical<?
  (syntax-rules ()
    [(_ [<?1 x1 y1] [<?2 x2 y2])
     (cond
       [(<?1 x1 y1) #t]
       [(<?1 y1 x1) #f]
       [(<?2 x2 y2) #t]
       [else #f])]
    [(_ [<?1 x1 y1] [<?2 x2 y2] [<?s xs ys] ...)
     (cond
       [(<?1 x1 y1) #t]
       [(<?1 y1 x1) #f]
       [else
        (lexical<? [<?2 x2 y2] [<?s xs ys] ...)])]))

(: atom<? (-> ATOM ATOM Boolean))
(define (atom<? a1 a2)
  (cond
    [(eq? a1 a2) #f]
    [else
     (define hc1 (eq-hash-code a1))
     (define hc2 (eq-hash-code a2))
     (cond
       [(unsafe-fx< hc1 hc2) #t]
       [(unsafe-fx> hc1 hc2) #f]
       [else (lexical<? [type<? (car a1) (car a2)]
                        [type<? (cdr a1) (cdr a2)])])]))

(: bdd<? (-> BDD BDD Boolean))
(define (bdd<? b1 b2)
  (cond
    [(eq? b1 b2) #f]
    [(eq? b2 'TOP) #t]
    [(eq? b2 'BOT) #f]
    [(eq? b1 'TOP) #f]
    [(eq? b1 'BOT) #t]
    [else
     (define hc1 (eq-hash-code b1))
     (define hc2 (eq-hash-code b2))
     (cond
       [(unsafe-fx< hc1 hc2) #t]
       [(unsafe-fx> hc1 hc2) #f]
       [else (lexical<? [atom<? (NODE-atom b1) (NODE-atom b2)]
                        [bdd<? (NODE-left b1) (NODE-left b2)]
                        [bdd<? (NODE-middle b1) (NODE-middle b2)]
                        [bdd<? (NODE-right b1) (NODE-right b2)])])]))


(: type<? (-> TYPE TYPE Boolean))
(define (type<? t1 t2)
  (define hc1 (eq-hash-code t1))
  (define hc2 (eq-hash-code t2))
  (cond
    [(unsafe-fx< hc1 hc2) #t]
    [(unsafe-fx> hc1 hc2) #f]
    [else (lexical<? [unsafe-fx< (BASE-data (TYPE-base t1))
                                 (BASE-data (TYPE-base t2))]
                     [bdd<? (TYPE-prods t1)  (TYPE-prods t2)]
                     [bdd<? (TYPE-arrows t1) (TYPE-arrows t2)])]))
