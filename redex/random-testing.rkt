#lang racket

;; Random testing of the numeric primitive ops

(require redex/reduction-semantics
         math/base
         (rename-in racket [eval racket/base:eval])
         "lang-semantics.rkt"
         "haskell.rkt"
         "lang-testing.rkt"
         "random-real.rkt")

(caching-enabled? #f)

(define (rand-I)
  (match (random 26)
    ;; Zero
    [(or 0 1 2) 0]
    ;; One
    [(or 3 4 5) 1]
    ;; ByteLargerThanOne
    [6 2]
    [7 255]
    [(or 8 9) (random 2 256)]
    ;; PosIndexNotByte
    [10 256]
    [11 1152921504606846975]
    [(or 12 13) (random-integer 256 1152921504606846976)]
    ;; PosFixnumNotIndex
    [14 1152921504606846976]
    [15 4611686018427387903]
    [(or 16 17) (random-integer 1152921504606846976
                                4611686018427387904)]
    ;; PosIntegerNotFixnum
    [(or 18 19) (random-integer 4611686018427387903
                                9999999999999999999)]
    ;; NegFixnum
    [20 -1]
    [21 -4611686018427387904]
    [(or 22 23) (random-integer -4611686018427387904
                                0)]
    ;; NegIntegerNotFixnum
    [(or 24 25) (random-integer -9999999999999999999
                                -4611686018427387905)]))

(define (rand-R)
  (if (zero? (random 2))
      (random-integer->random-real
       (random-integer -9999999999999999999
                       9999999999999999999))
      (random-integer->random-real
       (random 4294967087))))

(define (rand-N)
  (match (random 9)
    [(or 0 1 2) (rand-I)]
    [(or 3 4 5) (rand-R)]
    [6 (+ (sqrt (rand-R))
          (sqrt (rand-R)))]
    [7 (- (sqrt (rand-R))
          (sqrt (rand-R)))]
    [8 (* (sqrt (rand-R))
          (sqrt (rand-R)))]))

(define numeric-base-type-symbols
  '(Zero
    One
    ByteLargerThanOne
    PosIndexNotByte
    PosFixnumNotIndex
    NegFixnum
    PosIntegerNotFixnum
    NegIntegerNotFixnum
    PosRationalNotInteger
    NegRationalNotInteger
    FloatNaN
    FloatPosZero
    FloatNegZero
    PosFloatNumber
    PosFloatInfinity
    NegFloatNumber
    NegFloatInfinity
    SingleFloatNaN
    SingleFloatPosZero
    SingleFloatNegZero
    PosSingleFloatNumber
    PosSingleFloatInfinity
    NegSingleFloatNumber
    NegSingleFloatInfinity
    ExactImaginary
    ExactComplex
    FloatImaginary
    SingleFloatImaginary
    FloatComplex
    SingleFloatComplex))
(define numeric-base-type-count
  (length numeric-base-type-symbols))
(define (random-ann num)
  (define num-type (term (const-type ,num)))
  (term (ann ,num ,(foldl (λ (t t*) (term (Or ,t ,t*)))
                          num-type
                          (take (shuffle numeric-base-type-symbols)
                                (random (add1 numeric-base-type-count)))))))

;; at least one value for each integer base type
(define int-values
  '(0 1 42 255 256 999 1999999999999999998 -1 -42
      9999999999999999999 -9999999999999999999))
;; at least one value for each real base type
(define real-values
  (append int-values
          '(1/2 -1/2 +nan.0 +0.0 -0.0 1.0 2.0 +inf.0
                -1.0 -2.0 -inf.0 +nan.f +0.0f0 -0.0f0
                1.0f0 +inf.f -1.0f0 -inf.f)))
;; at least one value for each number base type
(define num-values
  (append real-values
          '(0+123i 123+456i 0+123.456i 0+456.789f0i
                   789+123.456i 981.0f0+456.789f0i)))




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
          [else
           (inc! total-failed-random-tests)
           (printf "counterexample: ~a\n" exp)])])])
  )


(define (number->type n)
  (cond
    [(exact-integer? n) (term (int-type ,n))]
    [(real? n) (term (real-type ,n))]
    [else (term (num-type ,n))]))

(define (unary-fn-simple-tests fun args)
  (define (do-check arg)
    (printf ".") (flush-output)
    (check-big-step-soundness (list fun arg)))
  (printf "\n~a simple tests...\n" fun)
  (for ([arg (in-list args)])
    (do-check arg)
    (do-check (random-ann arg)))
  (printf "\n")
  (print-and-reset-individual-counters!))


(define (binary-fn-simple-tests fun args)
  (define (do-check arg1 arg2)
    (printf ".") (flush-output)
    (check-big-step-soundness (list fun arg1 arg2)))
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
    (do-check arg1 arg2)
    (do-check (random-ann arg1)
              (random-ann arg2)))
  (printf "\n")
  (print-and-reset-individual-counters!))


(define (comp-simple-tests comp-fn)
  (define (do-check arg1 arg2)
    (printf ".") (flush-output)
    (check-big-step-soundness
     (term (let [x ,arg1] (let [y ,arg2] (if (,comp-fn x y) x  #f)))))
    (check-big-step-soundness
     (term (let [x ,arg1] (let [y ,arg2] (if (,comp-fn x y) #f x)))))
    (check-big-step-soundness
     (term (let [x ,arg1] (let [y ,arg2] (if (,comp-fn x y) y #f)))))
    (check-big-step-soundness
     (term (let [x ,arg1] (let [y ,arg2] (if (,comp-fn x y) #f y))))))
  (printf "\n~a simple tests...\n" comp-fn)
  (for* ([arg1 (in-list real-values)]
         [arg2 (in-list real-values)])
    (do-check arg1 arg2))
  (for* ([arg1 (in-list real-values)]
         [arg2 (in-list real-values)]
         [arg1 (in-value (random-ann arg1))]
         [arg2 (in-value (random-ann arg2))])
    (do-check arg1 arg2))
  (printf "\n")
  (print-and-reset-individual-counters!))


(define (run-random-tests! n-attempts seed)
  (define (random-fn-soundness-check! function gen-args)
    (printf "\n~a random testing...\n" function)
    (for* ([_ (in-range n-attempts)]
           [args (in-value (gen-args))])
      (let* ([expr (cons function args)]
             [ann-expr (cons function (map random-ann args))])
        (printf ".") (flush-output)
        (unless (and (eq? function 'expt)
                     (not (andmap (λ (x) (or (and (real? x) (or (infinite? x) (nan? x)))
                                             (and (< -1000 (real-part x) 1000)
                                                  (< -1000 (imag-part x) 1000))))
                                  args)))
          (check-big-step-soundness expr)
          (check-big-step-soundness ann-expr))))
    (printf "\n")
    (print-and-reset-individual-counters!))
  (define (random-comp-check! comp-fn gen-arg)
    (printf "\n~a random testing...\n" comp-fn)
    (for* ([_ (in-range n-attempts)]
           [arg1 (in-value (gen-arg))]
           [ann-arg1 (in-value (random-ann arg1))]
           [arg2 (in-value (gen-arg))]
           [ann-arg2 (in-value (random-ann arg2))])
      (define (do-check arg1 arg2)
        (match (random 4)
          [0 (check-big-step-soundness
              (term (let [x ,arg1] (let [y ,arg2] (if (,comp-fn x y) x  #f)))))]
          [1 (check-big-step-soundness
              (term (let [x ,arg1] (let [y ,arg2] (if (,comp-fn x y) #f x)))))]
          [2 (check-big-step-soundness
              (term (let [x ,arg1] (let [y ,arg2] (if (,comp-fn x y) y  #f)))))]
          [3 (check-big-step-soundness
              (term (let [x ,arg1] (let [y ,arg2] (if (,comp-fn x y) #f y)))))]))
      (printf ".") (flush-output)
      (do-check arg1 arg2)
      (do-check ann-arg1 ann-arg2))
    (printf "\n")
    (print-and-reset-individual-counters!))
  ;; testing begins here
  (random-seed seed)
  (printf "random-testing seed: ~s\n" seed)
  (flush-output)
  (clear-counters!)
  ;(unary-fn-simple-tests 'add1 num-values)
  ;(random-fn-soundness-check! 'add1 (λ () (list (rand-N))))
  ;(unary-fn-simple-tests 'sub1 num-values)
  ;(random-fn-soundness-check! 'sub1 (λ () (list (rand-N))))
  ;(unary-fn-simple-tests 'abs real-values)
  ;(random-fn-soundness-check! 'abs (λ () (list (rand-R))))
  ;(unary-fn-simple-tests 'sqr num-values)
  ;(random-fn-soundness-check! 'sqr (λ () (list (rand-N))))
  ;(unary-fn-simple-tests 'sqrt num-values)
  ;(random-fn-soundness-check! 'sqrt (λ () (list (rand-N))))
  ;(binary-fn-simple-tests '+ num-values)
  ;(random-fn-soundness-check! '+ (λ () (list (rand-N) (rand-N))))
  ;(binary-fn-simple-tests '- num-values)
  ;(random-fn-soundness-check! '- (λ () (list (rand-N) (rand-N))))
  ;(binary-fn-simple-tests '* num-values)
  ;(random-fn-soundness-check! '* (λ () (list (rand-N) (rand-N))))
  ;(binary-fn-simple-tests '/ num-values)
  ;(random-fn-soundness-check! '/ (λ () (list (rand-N) (rand-N))))
  ;(binary-fn-simple-tests 'min real-values)
  ;(random-fn-soundness-check! 'min (λ () (list (rand-R) (rand-R))))
  ;(binary-fn-simple-tests 'max real-values)
  ;(random-fn-soundness-check! 'max (λ () (list (rand-R) (rand-R))))
  ;(binary-fn-simple-tests 'expt num-values)
  ;(random-fn-soundness-check! 'expt (λ () (list (rand-N) (rand-N))))
  ;(binary-fn-simple-tests 'quotient int-values)
  ;(random-fn-soundness-check! 'quotient (λ () (list (rand-I) (rand-I))))
  ;(binary-fn-simple-tests 'modulo int-values)
  ;(random-fn-soundness-check! 'modulo (λ () (list (rand-I) (rand-I))))
  ;(comp-simple-tests '<)
  ;(random-comp-check! '< rand-R)
  ;(comp-simple-tests '<=)
  ;(random-comp-check! '<= rand-R)
  (comp-simple-tests '=)
  (random-comp-check! '= rand-R)
  (cond
    [(zero? total-failed-random-tests)
     (printf "\nALL ~a TESTS PASSED!\n" total-random-tests)]
    [else
     (printf "\nTOTAL TESTS RUN: ~a\n" total-random-tests)
     (printf "FAILURES:        ~a\n" total-failed-random-tests)]))


(module+ test
  (run-random-tests! 100 (+ 1 (random 1 (expt 2 30)))))


(module+ main
  (define n-attempts 100)
  (define seed (+ 1 (random 1 (expt 2 30))))
  (command-line
   #:once-each
   [("-n") n "Number of attempts" (set! n-attempts (string->number n))]
   [("-s") s "RNG seed"           (set! seed (string->number s))])

  (run-random-tests! n-attempts seed))
