#lang typed/racket/base

(require "semantic-type-rep.rkt"
         "semantic-base-type-ops.rkt"
         racket/match)


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

(define Any-TYPE (type top-BASE 'TOP 'TOP))