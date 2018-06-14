#lang typed/racket/base

(require (only-in "syntactic-type-rep.rkt"
                  NUMERIC-BASE
                  numeric-base-list)
         racket/match
         (only-in racket/unsafe/ops
                  unsafe-fx<
                  unsafe-fx>
                  unsafe-fxand
                  unsafe-fxior
                  unsafe-fx=
                  unsafe-fxnot))

(provide (except-out (all-defined-out)
                     make-memo-entry
                     memo-table-construct))

(define-type (HT K V) (HashTable K V))

(define-syntax make-memo-entry
  (syntax-rules ()
    [(_ v) v]
    [(_ k v)
     (make-weak-hasheq
      (list ((ann cons (All (A B) (-> A B (Pair A B))))
             k v)))]
    [(_ k1 k2 . rest)
     (make-weak-hasheq
      (list (cons k1 (make-memo-entry k2 . rest))))]))

(define-syntax memo-table-construct
  (syntax-rules ()
    [(_ cur make-expr) cur]
    [(_ cur make-expr field rest ...)
     (let ([next (hash-ref cur field #f)])
       (cond
         [next (memo-table-construct next make-expr rest ...)]
         [else
          (define val make-expr)
          (define entry (make-memo-entry rest ... val))
          (hash-set! cur field entry)
          val]))]))



(: base-bit-table (HT NUMERIC-BASE Fixnum))
(define base-bit-table
  (for/hash : (HT NUMERIC-BASE Fixnum)
    ([sym : NUMERIC-BASE (in-list numeric-base-list)]
     [n : Natural (in-naturals 1)])
    (values sym (assert (arithmetic-shift #b1 n) fixnum?))))


(: symbols->bits (-> (Listof NUMERIC-BASE) Fixnum))
(define (symbols->bits syms)
  (foldl (λ ([sym : NUMERIC-BASE]
             [acc : Fixnum])
           (unsafe-fxior acc (hash-ref base-bit-table sym)))
         #b0
         syms))

(: symbols->BASE (-> (Listof NUMERIC-BASE) BASE))
(define (symbols->BASE syms)
  (base #t (symbols->bits syms)))

(define-syntax-rule (SIGN-MASK)
  #b1111111111111111111111111111110)
(define-syntax-rule (BIT-MASK)
  #b0000000000000000000000000000001)

(void
 (assert (SIGN-MASK) fixnum?)
 (assert (BIT-MASK) fixnum?))


(unless (eqv? (unsafe-fxior (SIGN-MASK) (BIT-MASK))
              (sub1 (arithmetic-shift 1 (add1 (length numeric-base-list)))))
  (error "masks and base-list out of sync"))

(: base-sign (-> BASE Boolean))
(define (base-sign b)
  (unsafe-fx= 0 (unsafe-fxand (BASE-data b) (SIGN-MASK))))

(: base-bits (-> BASE Fixnum))
(define (base-bits b)
  (unsafe-fxand (BASE-data b) (BIT-MASK)))

(: base (-> Boolean Fixnum BASE))
(define (base sign bits)
  (cond
    [sign (make-BASE (unsafe-fxior bits (BIT-MASK)))]
    [else (make-BASE bits)]))

(define-syntax-rule (unsafe-fxdiff bits1 bits2)
  (unsafe-fxand bits1 (unsafe-fxnot bits2)))

(: base-or (-> BASE BASE BASE))
(define (base-or b1 b2)
  (define bits1 (base-bits b1))
  (define bits2 (base-bits b2))
  (match* ((base-sign b1) (base-sign b2))
    [(#t #t) (base #t (unsafe-fxior  bits1 bits2))]
    [(#t #f) (base #f (unsafe-fxdiff bits1 bits2))]
    [(#f #t) (base #f (unsafe-fxdiff bits2 bits1))]
    [(#f #f) (base #f (unsafe-fxand  bits1 bits2))]))

(: base-and (-> BASE BASE BASE))
(define (base-and b1 b2)
  (define bits1 (base-bits b1))
  (define bits2 (base-bits b2))
  (match* ((base-sign b1) (base-sign b2))
    [(#t #t) (base #t (unsafe-fxand  bits1 bits2))]
    [(#t #f) (base #t (unsafe-fxdiff bits1 bits2))]
    [(#f #t) (base #t (unsafe-fxdiff bits2 bits1))]
    [(#f #f) (base #f (unsafe-fxior  bits1 bits2))]))

(: base-diff (-> BASE BASE BASE))
(define (base-diff b1 b2)
  (define bits1 (base-bits b1))
  (define bits2 (base-bits b2))
  (match* ((base-sign b1) (base-sign b2))
    [(#t #t) (base #t (unsafe-fxdiff bits1 bits2))]
    [(#t #f) (base #t (unsafe-fxand  bits1 bits2))]
    [(#f #t) (base #t (unsafe-fxior  bits2 bits1))]
    [(#f #f) (base #t (unsafe-fxior  bits2 bits1))]))


(define-type ATOM (Pair TYPE TYPE))

(: atom (-> TYPE TYPE ATOM))
(define atom
  (let ([atom-table : (HT TYPE (HT TYPE (Pair TYPE TYPE)))
                    (make-weak-hasheq)])
    (λ (a d)
      (memo-table-construct atom-table (cons a d) a d))))

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
      (memo-table-construct node-table (NODE a l m r) a l m r))))

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
  (let ([base-table : (HT BASE BASE) (make-weak-hash)])
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
      (memo-table-construct type-table (TYPE b p a) b p a))))

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

(: base<? (-> BASE BASE Boolean))
(define (base<? b1 b2)
  (cond
    [(eq? b1 b2) #f]
    [else
     (define hc1 (eq-hash-code b1))
     (define hc2 (eq-hash-code b2))
     (cond
       [(unsafe-fx< hc1 hc2) #t]
       [(unsafe-fx> hc1 hc2) #f]
       [else (unsafe-fx< (BASE-data b1) (BASE-data b2))])]))

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
    [else (lexical<? [base<? (TYPE-base t1)   (TYPE-base t2)]
                     [bdd<?  (TYPE-prods t1)  (TYPE-prods t2)]
                     [bdd<?  (TYPE-arrows t1) (TYPE-arrows t2)])]))



(: node (-> (Pair TYPE TYPE) BDD BDD BDD BDD))
(define (node a l m r)
  (cond
    [(eq? m 'TOP) 'TOP]
    [(eq? l r) (bdd-or l m)]
    [else (make-NODE a l m r)]))

(: bdd-or (-> BDD BDD BDD))
(define (bdd-or b1 b2)
  (match* (b1 b2)
    [(_ _) #:when (eq? b1 b2) b1]
    [(_ 'TOP) 'TOP]
    [('TOP _) 'TOP]
    [(b 'BOT) b]
    [('BOT b) b]
    [((NODE a1 l1 m1 r1) (NODE a2 l2 m2 r2))
     #:when (eq? a1 a2)
     (node a1 (bdd-or l1 l2) (bdd-or m1 m2) (bdd-or r1 r2))]
    [((NODE a1 l1 m1 r1) (NODE a2 _ _ _))
     #:when (atom<? a1 a2)
     (node a1 l1 (bdd-or m1 b2) r1)]
    [((NODE _ _ _ _) (NODE a2 l2 m2 r2))
     (node a2 l2 (bdd-or m2 b1) r2)]))


(: bdd-and (-> BDD BDD BDD))
(define (bdd-and b1 b2)
  (match* (b1 b2)
    [(_ _) #:when (eq? b1 b2) b1]
    [(b 'TOP) b]
    [('TOP b) b]
    [(_ 'BOT) 'BOT]
    [('BOT _) 'BOT]
    [((NODE a1 l1 m1 r1) (NODE a2 l2 m2 r2))
     #:when (eq? a1 a2)
     (node a1
           (bdd-and (bdd-or l1 m1)
                    (bdd-or l2 m2))
           'BOT
           (bdd-and (bdd-or r1 m1)
                    (bdd-or r2 m2)))]
    [((NODE a1 l1 m1 r1) (NODE a2 _ _ _))
     #:when (atom<? a1 a2)
     (node a1 (bdd-and l1 b2) (bdd-and m1 b2) (bdd-and r1 b2))]
    [((NODE _ _ _ _) (NODE a2 l2 m2 r2))
     (node a2 (bdd-and b1 l2) (bdd-and b1 m2) (bdd-and b1 r2))]))

(: bdd-diff (-> BDD BDD BDD))
(define (bdd-diff b1 b2)
  (match* (b1 b2)
    [(_ _) #:when (eq? b1 b2) 'BOT]
    [(b 'TOP) 'BOT]
    [('TOP b) (bdd-not b)]
    [(b 'BOT) b]
    [('BOT _) 'BOT]
    [((NODE a1 l1 m1 r1) (NODE a2 _ _ _))
     #:when (eq? a1 a2)
     (node a1
           (bdd-diff l1 b2)
           (bdd-diff m1 b2)
           (bdd-diff r1 b2))]
    [((NODE a1 l1 m1 r1) (NODE a2 _ _ _))
     #:when (atom<? a1 a2)
     (node a1
           (bdd-diff (bdd-or l1 m1) b2)
           'BOT
           (bdd-diff (bdd-or r1 m1) b2))]
    [((NODE _ _ _ _) (NODE a2 l2 m2 r2))
     (node a2
           (bdd-diff b1 (bdd-or l2 m2))
           'BOT
           (bdd-diff b1 (bdd-or r2 m2)))]))

(: bdd-not (-> BDD BDD))
(define (bdd-not b)
  (match b
    ['TOP 'BOT]
    ['BOT 'TOP]
    [(NODE a l m 'BOT)
     (define ¬m (bdd-not m))
     (node a 'BOT (bdd-or l ¬m) ¬m)]
    [(NODE a 'BOT m r)
     (define ¬m (bdd-not m))
     (node a ¬m (bdd-or ¬m r) 'BOT)]
    ;; is this third clause unnecessary???
    ;; I think so...
    ;[(NODE a l 'BOT r)
    ; (define ¬l (bdd-not l))
    ; (define ¬r (bdd-not r))
    ; ;; TODO (bdd-or ¬l r) => 'BOT ???
    ; (node a ¬l (bdd-or ¬l r) ¬r)]
    [(NODE a l m r)
     (define ¬l (bdd-not l))
     (define ¬r (bdd-not r))
     (node a (bdd-or ¬l m) 'BOT (bdd-or ¬r m))]))

(: type-and (-> TYPE TYPE TYPE))
(define (type-and t1 t2)
  (match* (t1 t2)
    [((TYPE b1 p1 a1) (TYPE b2 p2 a2))
     (type (base-and b1 b2)
           (bdd-and p1 p2)
           (bdd-and a1 a2))]))

(: type-or (-> TYPE TYPE TYPE))
(define (type-or t1 t2)
  (match* (t1 t2)
    [((TYPE b1 p1 a1) (TYPE b2 p2 a2))
     (type (base-or b1 b2)
           (bdd-or p1 p2)
           (bdd-or a1 a2))]))

(: type-diff (-> TYPE TYPE TYPE))
(define (type-diff t1 t2)
  (match* (t1 t2)
    [((TYPE b1 p1 a1) (TYPE b2 p2 a2))
     (type (base-diff b1 b2)
           (bdd-diff p1 p2)
           (bdd-diff a1 a2))]))

(: type-not (-> TYPE TYPE))
(define (type-not t)
  (type-diff Any-TYPE t))








(define top-BASE (base #f #b0))
(define bot-BASE (base #t #b0))

(define Any-TYPE (type top-BASE 'TOP 'TOP))
(define Empty-TYPE (type bot-BASE 'BOT 'BOT))
(define Any-Base-TYPE (type top-BASE 'BOT 'BOT))
(define Any-Prod-TYPE (type bot-BASE 'TOP 'BOT))
(define Any-Arrow-TYPE (type bot-BASE 'BOT 'TOP))


(: Arrow-TYPE (-> TYPE TYPE TYPE))
(define (Arrow-TYPE t1 t2)
  (type bot-BASE 'BOT (node (cons t1 t2) 'TOP 'BOT 'BOT)))

(: Prod-TYPE (-> TYPE TYPE TYPE))
(define (Prod-TYPE t1 t2)
  (type bot-BASE (node (cons t1 t2) 'TOP 'BOT 'BOT) 'BOT))
