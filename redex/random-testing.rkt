#lang racket

;; Random testing of the numeric primitive ops

(require redex/reduction-semantics
         "lang-syntax.rkt"
         "lang-semantics.rkt"
         "haskell.rkt"
         "lang-testing.rkt")


(define-language sot-math
  [i integer]
  [r real]
  [n number]
  [nop1 ::= add1 sub1 abs sqr sqrt]
  [nop2 ::= + - * / min max expt quotient modulo]
  ;; integer operators
  [I ::=
     (quotient i i)
     (modulo i i)]
  ;; real operators
  [R ::=
     (abs r)
     (min r r)
     (max r r)]
  ;; number operators
  [N ::=
     (add1 n)
     (sub1 n)
     (sqr  n)
     (sqrt n)
     (+ n n)
     (- n n)
     (* n n)
     (/ n n)
     (expt n n)]
  [INEQ < <=]
  [EQ   =]
  [C (let (x r) (let (y r) (if (INEQ x y) x  #f)))
     (let (x r) (let (y r) (if (INEQ x y) #f x)))
     (let (x r) (let (y r) (if (INEQ x y) y #f)))
     (let (x r) (let (y r) (if (INEQ x y) #f y)))
     (let (x n) (let (y n) (if (EQ   x y) x  #f)))
     (let (x n) (let (y n) (if (EQ   x y) #f x)))
     (let (x n) (let (y n) (if (EQ   x y) y #f)))
     (let (x n) (let (y n) (if (EQ   x y) #f y)))])

;; state for tracking test data
(define total-random-tests 0)
(define total-failed-random-tests 0)
(define tries 0)
(define trapped-errors 0)
(define type-errors 0)
(define-syntax-rule (inc! id)
  (set! id (add1 id)))
(define (clear-counters!)
  (set! tries 0)
  (set! trapped-errors 0)
  (set! type-errors 0))
(define (print-and-reset-individual-counters!)
  (printf "  tries: ~a\n  trapped-errors: ~a\n  type-errors: ~a\n  successes: ~a\n"
          tries
          trapped-errors
          type-errors
          (- tries trapped-errors type-errors))
  (clear-counters!))

;; ensure well-typed expressions evaluate and either:
;; - produce a trapped error
;; - produce a value of the predicted type
(define (check-big-step-soundness exp)
  (inc! tries)
  (inc! total-random-tests)
  ;; type check the expression
  (define type-check-result
    (judgment-holds (synth EnvNull ⊢ ,exp : (Res τ _ _ _)) τ))
  ;; evaluate the expression
  (define evaluation-result
    (judgment-holds (valof ,initial-evaluation-fuel
                           (;) RhoNull ⊢ ,exp ⇓ RESULT)
                    RESULT))
  (match* (type-check-result
           evaluation-result)
    ;; ill-typed expression we ignore
    [('() _) (inc! type-errors) #true]
    ;; all well-typed expressions should evaluate in our big-step semantics!
    [((list type) '()) (error 'soundness
                              "failed evaluation for expression: ~a\n had type: ~a"
                              exp
                              type)]
    ;; we shouldn't get timeout
    [((list type) '(TIMEOUT)) (error 'soundness "TIMOUT for expression: ~a" exp)]
     ;; a well-typed expression should not get stuck!
    [((list type) '(STUCK)) (inc! total-failed-random-tests) #false]
    ;; "trapped runtime errors" are fine
    [((list type) '(ERROR)) (inc! trapped-errors) #true]
    [((list type) (list val))
     (match (judgment-holds (synth-val ⊢v ,val : τ) τ)
       [(list val-type)
        (cond
          [(Subtype val-type type) #true]
          [else (inc! total-failed-random-tests) #false])])])
  )


(define (number->type n)
  (cond
    [(exact-integer? n) (term (int-type ,n))]
    [(real? n) (term (real-type ,n))]
    [else (term (num-type ,n))]))

(define (run-random-tests! n-attempts seed)
  (define-syntax-rule (soundness-check! title pattern)
    (begin
      (printf "~a in-order testing...\n" title)
      (redex-check sot-math pattern #:in-order
                   (check-big-step-soundness (term pattern))
                   #:attempts n-attempts
                   #:print? #false)
      (print-and-reset-individual-counters!)
      (printf "~a ad-hoc testing...\n" title)
      (redex-check sot-math pattern #:ad-hoc
                   (check-big-step-soundness (term pattern))
                   #:attempts n-attempts
                   #:print? #false)
      (print-and-reset-individual-counters!)))
  (random-seed seed)
  (printf "random-testing seed: ~s\n" seed)
  (flush-output)
  (clear-counters!)
  (printf "checking numeric base types metafunction...\n")
  (redex-check sot-math number #:in-order
               (eq? (lookup-number-type (term number))
                    (number->type (term number)))
               #:attempts n-attempts
               #:print? #false)
  (redex-check sot-math number #:ad-hoc
               (eq? (lookup-number-type (term number))
                    (number->type (term number)))
               #:attempts n-attempts
               #:print? #false)
  (soundness-check! "integer" I)
  (soundness-check! "real" R)
  (soundness-check! "number" N)
  (soundness-check! "comparison" C)
  (cond
    [(zero? total-failed-random-tests)
     (printf "\nALL ~a TESTS PASSED!\n" total-random-tests)]
    [else
     (printf "\nTOTAL TESTS RUN: ~a\n" total-random-tests)
     (printf "FAILURES:        ~a\n" total-failed-random-tests)]))


(module+ test
  (run-random-tests! 1000 (+ 1 (random 1 (expt 2 30)))))


(module+ main
  (define n-attempts 1000)
  (define seed (+ 1 (random 1 (expt 2 30))))
  (command-line
   #:once-each
   [("-n") n "Number of attempts" (set! n-attempts (string->number n))]
   [("-s") s "RNG seed"           (set! seed (string->number s))])

  (run-random-tests! n-attempts seed))
