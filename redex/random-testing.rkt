#lang racket

;; Random testing of the numeric primitive ops

(require redex/reduction-semantics
         (rename-in racket [eval racket/base:eval])
         "lang-semantics.rkt"
         "haskell.rkt"
         "lang-testing.rkt"
         "random-real.rkt")

(caching-enabled? #f)

;; at least one ineger value for each integer base type
(define int-values
  '(0 1 42 255 256 999 1999999999999999998 -1 -42
      9999999999999999999 -9999999999999999999))

;; at least one ineger value for each real base type
(define real-values
  (append int-values
          '(1/2 -1/2 +nan.0 +0.0 -0.0 1.0 2.0 +inf.0
                -1.0 -2.0 -inf.0 +nan.f +0.0f0 -0.0f0
                1.0f0 +inf.f -1.0f0 -inf.f)))

;; at least one ineger value for each number base type
(define num-values
  (append real-values
          '(0+123i 123+456i 0+123.456i 0+456.789f0i
                   789+123.456i 981.0f0+456.789f0i)))

(define-language random-numbers
  ;; more likely to be integers
  [I* (exact-round real) I]
  [I ::=
     (* I* I* ...)
     (+ I* I* ...)
     (- I* I* ...)
     (bitwise-and I* ...)
     (bitwise-ior I* ...)
     (bitwise-xor I* ...)
     (bitwise-not I*)
     0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20
     110 111 112 113 114 115 116 117 118 119 1110 1111
     1112 1113 1114 1115 1116 1117 1118 1119 1120
     42
     999   
     -1
     9999999999999999999
     -9999999999999999999]
  ;; more likely to be floats
  [F* (real->double-flonum real) F]
  [F (* F* F* ...)
     (+ F* F* ...)
     (- F* F* ...)
     (/ F* F* ...)
     (cos F*)
     (sin F*)
     (tan F*)
     (sqr F*)
     0.115 1.44 2.3 3.2 4.243 5.543 6.33 7.123 8.543
     9.1234 10.5436
     11.324 12.543 13.0 14.5 15.99 16.12 17.544 18.13
     19.132 20.432
     110.0 111.0 112.0 113.0 114.0 115.0 116.0
     117.0 118.0 119.0 1110.0 1111.0
     1112.04322 1113.043252 1114.0432 1115.4324
     1116.423 1117.0234
     1118.04233 1119.0423432 1120.32123
     +nan.0
     +0.0
     -0.0
     1.0
     42.0
     +inf.0
     -1.0
     -42.0
     -inf.0
     +nan.f
     +0.0f0
     -0.0f0
     1.0f0
     420.0f0
     +inf.f
     -1.0f0
     -420.0f0
     -inf.f]
  [R ::= I F
     1/2 5/9 123/456
     1111/22222222
     4247834/3982489
     -1/2
     -13/44
     -1111/2222222
     -99812379/2222222]
  [N* real R N F S
      0+123i
      123+456i
      0+123.456i
      0+456.789f0i
      789+123.456i
      981.0f0+456.789f0i]
  [N (* N* N* ...)
     (+ N* N* ...)
     (- N* N* ...)
     (sqrt N*)]
  ;; not many single-flonum-specific ops, so will mostly be used in E context
  [S (real->single-flonum real)
     (inexact->exact S)
     (real->double-flonum S)]
  [COMP < <= =]
  [C (let [x R] (let [y R] (if (COMP x y) x  #f)))
     (let [x R] (let [y R] (if (COMP x y) #f x)))
     (let [x R] (let [y R] (if (COMP x y) y #f)))
     (let [x R] (let [y R] (if (COMP x y) #f y)))])


;; Redex allegedly can't generate reals, so we convert ints to reals.
(define (exp->real-exp E) ; numbers or symbols or lists
  (cond [(number? E)
         (random-integer->random-real
          (exact-round
           ;; doesn't handle non-rationals
           ;; not a problem, we generate those specially
           (if (rational? E)
               E
               0)))] ; arbitrary
        [(list? E) (map exp->real-exp E)]
        [else E]))

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

(define (evaluate expr)
  (with-handlers ([(λ _ #t) (λ _ (inc! trapped-errors) #f)])
    (racket/base:eval expr nspace)))

;; ensure well-typed expressions evaluate and either:
;; - produce a trapped error
;; - produce a value of the predicted type
(define (check-big-step-soundness exp)
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
    [('() _) #;(error 'check-big-step-soundness
                    "~a failed to type check!"
                    exp)
             (inc! type-errors)
             #true]
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

(define (unary-fn-simple-tests fun args)
  (printf "\n~a simple tests...\n" fun)
  (for ([arg (in-list args)])
    (printf ".") (flush-output)
    (inc! tries)
    (inc! total-random-tests)
    (check-big-step-soundness (list fun arg)))
  (printf "\n")
  (print-and-reset-individual-counters!))


(define (binary-fn-simple-tests fun args)
  (printf "\n~a simple tests...\n" fun)
  (for* ([arg1 (in-list args)]
         [arg2 (in-list args)]
         #:when
         ;; lets just not do exponentiation with big numbers...
         ;; it takes... a little while...
         (or (not (eq? fun 'expt))
             (andmap (λ (x) (or (and (real? x) (or (infinite? x) (nan? x)))
                                (and (< -1000 (real-part x) 1000)
                                     (< -1000 (imag-part x) 1000))))
                     (list arg1 arg2))))
    (printf ".") (flush-output)
    (inc! tries)
    (inc! total-random-tests)
    (check-big-step-soundness (list fun arg1 arg2)))
  (printf "\n")
  (print-and-reset-individual-counters!))


(define (comp-simple-tests comp-fn)
  (printf "\n~a simple tests...\n" comp-fn)
  (for* ([arg1 (in-list real-values)]
         [arg2 (in-list real-values)])
    (printf ".") (flush-output)
    (inc! tries)
    (inc! total-random-tests)
    (check-big-step-soundness
     (term (let [x ,arg1] (let [y ,arg2] (if (,comp-fn x y) x  #f)))))
    (inc! tries)
    (inc! total-random-tests)
    (check-big-step-soundness
     (term (let [x ,arg1] (let [y ,arg2] (if (,comp-fn x y) #f x)))))
    (inc! tries)
    (inc! total-random-tests)
    (check-big-step-soundness
     (term (let [x ,arg1] (let [y ,arg2] (if (,comp-fn x y) y #f)))))
    (inc! tries)
    (inc! total-random-tests)
    (check-big-step-soundness
     (term (let [x ,arg1] (let [y ,arg2] (if (,comp-fn x y) #f y))))))
  (printf "\n")
  (print-and-reset-individual-counters!))


(define (run-random-tests! n-attempts seed)
  (define-syntax-rule (random-fn-soundness-check! function arg-list-pattern)
    (begin
      (define-syntax-rule (fn-redex-check mode-kw)
        (redex-check
         random-numbers arg-list-pattern mode-kw
         (let* ([args (evaluate (cons 'list (term arg-list-pattern)))]
                [expr (cons 'function args)])
           (inc! tries)
           (inc! total-random-tests)
           (printf ".") (flush-output)
           (or (not args)
               ;; um... lets just not do exponentiation with big numbers...
               ;; it takes... a little while...
               (and (eq? 'function 'expt) (not (andmap (λ (x) (or (and (real? x) (or (infinite? x) (nan? x)))
                                                                  (and (< -1000 (real-part x) 1000)
                                                                       (< -1000 (imag-part x) 1000))))
                                                       args)))
               (check-big-step-soundness expr)))
         #:attempts n-attempts
         #:prepare exp->real-exp
         #:keep-going? #true
         #:print? #true))
      (printf "\n~a in-order testing...\n" 'function)
      (fn-redex-check #:in-order)
      (printf "\n")
      (print-and-reset-individual-counters!)
      (printf "\n~a ad-hoc testing...\n" 'function)
      (fn-redex-check #:ad-hoc)
      (printf "\n")
      (print-and-reset-individual-counters!)))
  (define (random-comp-check! comp-fn)
    (define-syntax-rule (comp-redex-check mode-kw)
      (redex-check
       random-numbers (R_1 R_2) mode-kw
       (let ([arg1 (evaluate (term R_1))]
             [arg2 (evaluate (term R_2))])
         (inc! tries)
         (inc! total-random-tests)
         (printf ".") (flush-output)
         (or (not (real? arg1))
             (not (real? arg2))
             (match (random 4)
               [0 (check-big-step-soundness
                   (term (let [x ,arg1] (let [y ,arg2] (if (,comp-fn x y) x  #f)))))]
               [1 (check-big-step-soundness
                   (term (let [x ,arg1] (let [y ,arg2] (if (,comp-fn x y) #f x)))))]
               [2 (check-big-step-soundness
                   (term (let [x ,arg1] (let [y ,arg2] (if (,comp-fn x y) y  #f)))))]
               [3 (check-big-step-soundness
                   (term (let [x ,arg1] (let [y ,arg2] (if (,comp-fn x y) #f y)))))])))
       #:attempts n-attempts
       #:prepare exp->real-exp
       #:keep-going? #true
       #:print? #true))
    (printf "\n~a in-order testing...\n" comp-fn)
    (comp-redex-check #:in-order)
    (printf "\n")
    (print-and-reset-individual-counters!)
    (printf "\n~a ad-hoc testing...\n" 'function)
    (comp-redex-check #:ad-hoc)
    (printf "\n")
    (print-and-reset-individual-counters!))
  ;; testing begins here
  (random-seed seed)
  (printf "random-testing seed: ~s\n" seed)
  (flush-output)
  (clear-counters!)
  (unary-fn-simple-tests 'add1 num-values)
  (random-fn-soundness-check! add1 (N))
  (unary-fn-simple-tests 'sub1 num-values)
  (random-fn-soundness-check! sub1 (N))
  (unary-fn-simple-tests 'abs real-values)
  (random-fn-soundness-check! abs (R))
  (unary-fn-simple-tests 'sqr num-values)
  (random-fn-soundness-check! sqr (N))
  (unary-fn-simple-tests 'sqrt num-values)
  (random-fn-soundness-check! sqrt (N))
  (binary-fn-simple-tests '+ num-values)
  (random-fn-soundness-check! + (N_1 N_2))
  (binary-fn-simple-tests '- num-values)
  (random-fn-soundness-check! - (N_1 N_2))
  (binary-fn-simple-tests '* num-values)
  (random-fn-soundness-check! * (N_1 N_2))
  (binary-fn-simple-tests '/ num-values)
  (random-fn-soundness-check! / (N_1 N_2))
  (binary-fn-simple-tests 'min real-values)
  (random-fn-soundness-check! min (R_1 R_2))
  (binary-fn-simple-tests 'max real-values)
  (random-fn-soundness-check! max (R_1 R_2))
  (binary-fn-simple-tests 'expt num-values)
  (random-fn-soundness-check! expt (N_1 N_2))
  (binary-fn-simple-tests 'quotient int-values)
  (random-fn-soundness-check! quotient (I_1 I_2))
  (binary-fn-simple-tests 'modulo int-values)
  (random-fn-soundness-check! modulo (I_1 I_2))
  (comp-simple-tests '<)
  (random-comp-check! '<)
  (comp-simple-tests '<=)
  (random-comp-check! '<=)
  (comp-simple-tests '=)
  (random-comp-check! '=)
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
