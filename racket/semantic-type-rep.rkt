#lang typed/racket/base

(require (only-in "syntactic-type-rep.rkt"
                  NUMERIC-BASE
                  numeric-base-list)
         (for-syntax racket/base)
         racket/match
         (only-in racket/unsafe/ops
                  unsafe-fx+
                  unsafe-fx<
                  unsafe-fx>
                  unsafe-fxand
                  unsafe-fxior
                  unsafe-fxxor
                  unsafe-fxlshift
                  unsafe-fxrshift
                  unsafe-fx=
                  unsafe-fxnot))

(provide (all-defined-out))

(define-type (HT K V) (HashTable K V))


#|
;; random primes with 60 bits
137139276007508911
1049307376606978823
104910382219104389
|#

;; 60 bit number (fixnum? on 64 bit) with random half 0s and half 1s
(define-syntax-rule (RANDOM-MASK)
  634984049258069545)

(define-syntax hash+
  (syntax-rules ()
    [(_ hc) hc]
    [(_ hc1 hcs ...) (unsafe-fx+ hc1 (hash+ hcs ...))]))

(define-syntax combine-hashes
  (syntax-rules ()
    [(combine-hashes seed) seed]
    [(combine-hashes seed hc)
     (unsafe-fxxor
      seed
      (hash+ hc
             (RANDOM-MASK)
             (unsafe-fxlshift seed 6)
             (unsafe-fxrshift seed 2)))]
    [(combine-hashes seed hcs ...)
     (combine-hashes seed (combine-hashes hcs ...))]))


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

(: symbols->BASE (-> (Listof NUMERIC-BASE) Fixnum))
(define (symbols->BASE syms)
  (base #t (symbols->bits syms)))

(define-syntax-rule (SIGN-MASK)
  #b0000000000000000000000000000001)
(define-syntax-rule (BIT-MASK)
  #b1111111111111111111111111111110)

(void
 (assert (SIGN-MASK) fixnum?)
 (assert (BIT-MASK) fixnum?))


(unless (eqv? (unsafe-fxior (SIGN-MASK) (BIT-MASK))
              (sub1 (arithmetic-shift 1 (add1 (length numeric-base-list)))))
  (error "masks and base-list out of sync"))

(: base-sign (-> Fixnum Boolean))
(define (base-sign b)
  (not (unsafe-fx= 0 (unsafe-fxand b (SIGN-MASK)))))

(: base-bits (-> Fixnum Fixnum))
(define (base-bits b)
  (unsafe-fxand b (BIT-MASK)))

(: base (-> Boolean Fixnum Fixnum))
(define (base sign bits)
  (cond
    [sign (unsafe-fxior bits (SIGN-MASK))]
    [else bits]))

(define-syntax-rule (unsafe-fxdiff bits1 bits2)
  (unsafe-fxand bits1 (unsafe-fxnot bits2)))

(: base-or (-> Fixnum Fixnum Fixnum))
(define (base-or b1 b2)
  (define bits1 (base-bits b1))
  (define bits2 (base-bits b2))
  (match* ((base-sign b1) (base-sign b2))
    [(#t #t) (base #t (unsafe-fxior  bits1 bits2))]
    [(#t #f) (base #f (unsafe-fxdiff bits1 bits2))]
    [(#f #t) (base #f (unsafe-fxdiff bits2 bits1))]
    [(#f #f) (base #f (unsafe-fxand  bits1 bits2))]))

(: base-and (-> Fixnum Fixnum Fixnum))
(define (base-and b1 b2)
  (define bits1 (base-bits b1))
  (define bits2 (base-bits b2))
  (match* ((base-sign b1) (base-sign b2))
    [(#t #t) (base #t (unsafe-fxand  bits1 bits2))]
    [(#t #f) (base #t (unsafe-fxdiff bits1 bits2))]
    [(#f #t) (base #t (unsafe-fxdiff bits2 bits1))]
    [(#f #f) (base #f (unsafe-fxior  bits1 bits2))]))

(: base-diff (-> Fixnum Fixnum Fixnum))
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
(define atom cons)

(struct REP ([hash : Fixnum]) #:transparent)

(struct TOP REP ())
;; do NOT create another instance
(define top (TOP (assert 14755516491509597 fixnum?))) ;; prime

(struct BOT REP ())
;; do NOT create another instance
(define bot (BOT (assert 654942626022799249 fixnum?))) ;; prime


(struct NODE REP
  ([atom : ATOM]
   [left : BDD]
   [middle : BDD]
   [right : BDD])
  #:transparent)

(: make-NODE (-> ATOM BDD BDD BDD
                 NODE))
(define (make-NODE a l m r)
  (define hc1 (REP-hash (car a)))
  (define hc2 (REP-hash (cdr a)))
  (define hc3 (REP-hash l))
  (define hc4 (REP-hash m))
  (define hc5 (REP-hash r))
  (NODE (combine-hashes hc1 hc2 hc3 hc4 hc5)
        a l m r))

(define-match-expander NODE:
  (λ (stx)
    (syntax-case stx ()
      [(_ a l m r) #'(NODE _ a l m r)])))

(define-type BDD (U TOP BOT NODE))


(struct TYPE REP ([base : Fixnum]
                  [prods : BDD]
                  [arrows : BDD])
  #:transparent)

(define-match-expander TYPE:
  (λ (stx)
    (syntax-case stx ()
      [(_ b p a) #'(TYPE _ b p a)])))

(: type (-> Fixnum BDD BDD TYPE))
(define (type b p a)
  (define hc2 (REP-hash p))
  (define hc3 (REP-hash a))
  (TYPE (combine-hashes b hc2 hc3) b p a))

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
    [else (lexical<? [type<? (car a1) (car a2)]
                     [type<? (cdr a1) (cdr a2)])]))

(: base<? (-> Fixnum Fixnum Boolean))
(define (base<? b1 b2)
  (unsafe-fx< b1 b2))

(: bdd<? (-> BDD BDD Boolean))
(define (bdd<? b1 b2)
  (define hc1 (REP-hash b1))
  (define hc2 (REP-hash b2))
  (match* (b1 b2)
    [(_ _) #:when (unsafe-fx< hc1 hc2) #t]
    [(_ _) #:when (unsafe-fx> hc1 hc2) #f]
    [(_ _) #:when (equal? b1 b2) #f]
    [((NODE: a1 l1 m1 r1) (NODE: a2 l2 m2 r2))
     (lexical<? [atom<? a1 a2]
                [bdd<? l1 l2]
                [bdd<? m1 m2]
                [bdd<? r1 r2])]))


(: type<? (-> TYPE TYPE Boolean))
(define (type<? t1 t2)
  (define hc1 (REP-hash t1))
  (define hc2 (REP-hash t2))
  (match* (t1 t2)
    [(_ _) #:when (unsafe-fx< hc1 hc2) #t]
    [(_ _) #:when (unsafe-fx> hc1 hc2) #f]
    [(_ _) #:when (equal? t1 t2) #f]
    [((TYPE: b1 p1 a1) (TYPE: b2 p2 a2))
     (lexical<? [unsafe-fx< b1 b2]
                [bdd<? p1 p2]
                [bdd<? a1 a2])]))



(: node (-> (Pair TYPE TYPE) BDD BDD BDD BDD))
(define (node a l m r)
  (cond
    [(eq? m top) top]
    [(equal? l r) (bdd-or l m)]
    [else (make-NODE a l m r)]))

(: bdd-or (-> BDD BDD BDD))
(define (bdd-or b1 b2)
  (match* (b1 b2)
    [(_ (== top eq?)) top]
    [((== top eq?) _) top]
    [(b (== bot eq?)) b]
    [((== bot eq?) b) b]
    [((NODE: a l1 m1 r1) (NODE: a l2 m2 r2))
     (cond
       [(and (equal? l1 l2)
             (equal? m1 m2)
             (equal? r1 r2))
        b1]
       [else
        (node a (bdd-or l1 l2) (bdd-or m1 m2) (bdd-or r1 r2))])]
    [((NODE: a1 l1 m1 r1) (NODE: a2 _ _ _))
     #:when (atom<? a1 a2)
     (node a1 l1 (bdd-or m1 b2) r1)]
    [((NODE: _ _ _ _) (NODE: a2 l2 m2 r2))
     (node a2 l2 (bdd-or m2 b1) r2)]))


(: bdd-and (-> BDD BDD BDD))
(define (bdd-and b1 b2)
  (match* (b1 b2)
    [(b (== top eq?)) b]
    [((== top eq?) b) b]
    [(_ (== bot eq?)) bot]
    [((== bot eq?) _) bot]
    [((NODE: a l1 m1 r1) (NODE: a l2 m2 r2))
     (cond
       [(and (equal? l1 l2)
             (equal? m1 m2)
             (equal? r1 r2))
        b1]
       [else
        (node a
              (bdd-and (bdd-or l1 m1)
                       (bdd-or l2 m2))
              bot
              (bdd-and (bdd-or r1 m1)
                       (bdd-or r2 m2)))])]
    [((NODE: a1 l1 m1 r1) (NODE: a2 _ _ _))
     #:when (atom<? a1 a2)
     (node a1 (bdd-and l1 b2) (bdd-and m1 b2) (bdd-and r1 b2))]
    [((NODE: _ _ _ _) (NODE: a2 l2 m2 r2))
     (node a2 (bdd-and b1 l2) (bdd-and b1 m2) (bdd-and b1 r2))]))

(: bdd-diff (-> BDD BDD BDD))
(define (bdd-diff b1 b2)
  (match* (b1 b2)
    [(b (== top eq?)) bot]
    [((== top eq?) b) (bdd-not b)]
    [(b (== bot eq?)) b]
    [((== bot eq?) _) bot]
    [((NODE: a l1 m1 r1) (NODE: a l2 m2 r2))
     (cond
       [(and (equal? l1 l2)
             (equal? m1 m2)
             (equal? r1 r2))
        bot]
       [else
        (node a
              (bdd-diff l1 b2)
              (bdd-diff m1 b2)
              (bdd-diff r1 b2))])]
    [((NODE: a1 l1 m1 r1) (NODE: a2 _ _ _))
     #:when (atom<? a1 a2)
     (node a1
           (bdd-diff (bdd-or l1 m1) b2)
           bot
           (bdd-diff (bdd-or r1 m1) b2))]
    [((NODE: _ _ _ _) (NODE: a2 l2 m2 r2))
     (node a2
           (bdd-diff b1 (bdd-or l2 m2))
           bot
           (bdd-diff b1 (bdd-or r2 m2)))]))

(: bdd-not (-> BDD BDD))
(define (bdd-not b)
  (match b
    [(== top eq?) bot]
    [(== bot eq?) top]
    [(NODE: a l m (== bot eq?))
     (node a bot (bdd-not (bdd-or l m)) (bdd-not m))]
    [(NODE: a (== bot eq?) m r)
     (node a (bdd-not m) (bdd-not (bdd-or m r)) bot)]
    [(NODE: a l (== bot eq?) r)
     (node a (bdd-not l) (bdd-not (bdd-or l r)) (bdd-not r))]
    [(NODE: a l m r)
     (node a (bdd-not (bdd-or l m)) bot (bdd-not (bdd-or r m)))]))

(: type-and (-> TYPE TYPE TYPE))
(define (type-and t1 t2)
  (match* (t1 t2)
    [((TYPE: b1 p1 a1) (TYPE: b2 p2 a2))
     (type (base-and b1 b2)
           (bdd-and p1 p2)
           (bdd-and a1 a2))]))

(: type-or (-> TYPE TYPE TYPE))
(define (type-or t1 t2)
  (match* (t1 t2)
    [((TYPE: b1 p1 a1) (TYPE: b2 p2 a2))
     (type (base-or b1 b2)
           (bdd-or p1 p2)
           (bdd-or a1 a2))]))

(: type-diff (-> TYPE TYPE TYPE))
(define (type-diff t1 t2)
  (match* (t1 t2)
    [((TYPE: b1 p1 a1) (TYPE: b2 p2 a2))
     (type (base-diff b1 b2)
           (bdd-diff p1 p2)
           (bdd-diff a1 a2))]))

(: type-not (-> TYPE TYPE))
(define (type-not t)
  (type-diff Any-TYPE t))





(define top-BASE (base #f #b0))
(define bot-BASE (base #t #b0))

(define Any-TYPE (type top-BASE top top))
(define Empty-TYPE (type bot-BASE bot bot))
(define Any-Base-TYPE (type top-BASE bot bot))
(define Any-Prod-TYPE (type bot-BASE top bot))
(define Any-Arrow-TYPE (type bot-BASE bot top))


(: Arrow-TYPE (-> TYPE TYPE TYPE))
(define (Arrow-TYPE t1 t2)
  (type bot-BASE bot (node (atom t1 t2) top bot bot)))

(: Prod-TYPE (-> TYPE TYPE TYPE))
(define (Prod-TYPE t1 t2)
  (type bot-BASE (node (atom t1 t2) top bot bot) bot))
