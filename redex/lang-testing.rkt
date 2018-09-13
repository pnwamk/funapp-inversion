#lang racket/base

(require redex/reduction-semantics
         racket/match
         "lang-syntax.rkt"
         "lang-semantics.rkt"
         (for-syntax racket/base))

(provide initial-evaluation-fuel)

(define-metafunction sot
  ORMACRO : e e -> e
  [(ORMACRO e_1 e_2) (let (tmp e_1) (if tmp tmp e_2))])
(define-metafunction sot
  ANDMACRO : e e -> e
  [(ANDMACRO e_1 e_2) (let (tmp e_1) (if tmp e_2 #false))])
(define-metafunction sot
  CONDMACRO : [e e] ... [else e] -> e
  [(CONDMACRO [e_1 e_2] [e_3 e_4] ... [else e_last])
   (if e_1
       e_2
       (CONDMACRO
        [e_3 e_4]
        ...
        [else e_last]))]
  [(CONDMACRO [else e_last]) e_last])

(define-metafunction sot
  ENV : p ... -> Γ
  [(ENV) EnvNull]
  [(ENV p q ...) (EnvSnoc (ENV q ...) p)])

(define-metafunction sot
  VALENV : [x v] ... -> ρ
  [(VALENV) RhoNull]
  [(VALENV [x v] any ...)
   (RhoSnoc (VALENV any ...)[x ↦ v])])

(define (equiv-types? t1 t2)
  (judgment-holds (≈ ,t1 ,t2)))

(define-for-syntax print-line-numbers #t)

(define-syntax (type-check-tests stx)
  (syntax-case stx ()
    [(_ . cases)
     (with-syntax
         ([(test ...)
           (for/list ([tst (in-list (syntax->list #'cases))])
             (syntax-case tst ()
               [(expr #:fail)
                (quasisyntax/loc tst
                  (begin
                    #,(if print-line-numbers
                          (quasisyntax/loc tst
                            (printf "type check test ~a...\n"
                                    #,(syntax-line tst)))
                          #'(void))
                    (test-equal (judgment-holds
                                 (synth EnvNull ⊢ expr : R)
                                 R)
                                '())))]
               [(#:env (p ...)
                 expr
                 #:fail)
                (quasisyntax/loc tst
                  (begin
                    #,(if print-line-numbers
                          (quasisyntax/loc tst
                            (printf "type check test ~a...\n"
                                    #,(syntax-line tst)))
                          #'(void))
                    (test-equal (judgment-holds
                               (synth (ENV p ...) ⊢ expr : R)
                               R)
                              '())))]
               [(expr type)
                (quasisyntax/loc tst
                  (begin
                    #,(if print-line-numbers
                          (quasisyntax/loc tst
                            (printf "type check test ~a...\n"
                                    #,(syntax-line tst)))
                          #'(void))
                    (match (judgment-holds
                            (synth EnvNull ⊢ expr : (Res τ _ _ _))
                            τ)
                      [(list t)
                       #,(syntax/loc tst
                           (test-equal t (term type) #:equiv equiv-types?))]
                      [otherwise
                       #,(syntax/loc tst
                           (test-equal
                            otherwise
                            (term type)))])))]
               [(#:env (p ...) expr type)
                (quasisyntax/loc tst
                  (begin
                    #,(if print-line-numbers
                          (quasisyntax/loc tst
                            (printf "type check test ~a...\n"
                                    #,(syntax-line tst)))
                          #'(void))
                    (match (judgment-holds
                          (synth (ENV p ...) ⊢ expr : (Res τ _ _ _))
                          τ)
                    [(list t)
                     #,(syntax/loc tst
                         (test-equal t (term type) #:equiv equiv-types?))]
                    [otherwise
                     #,(syntax/loc tst
                         (test-equal
                          otherwise
                          (term type)))])))]))])
       (syntax/loc stx
         (begin
           test ...)))]))

(module+ test
  (printf "-----------------------\n")
  (printf "TYPE CHECKING TESTS ...\n")
  (printf "-----------------------\n")
  (type-check-tests
   ;; constants
   [42 ByteLargerThanOne]
   ["42" String]
   [#true True]
   [#false False]

  
   ;; primitive unary operators
   ;; i.e. add1 sub1 abs
   [zero? (Arrow Number Boolean)]
   [string-length (Arrow String NonnegInteger)]
   [not (And (Arrow False True) (Arrow (Not False) False))]
   [exact-integer? (And (Arrow Integer True) (Arrow (Not Integer) False))]
   [string? (And (Arrow String True) (Arrow (Not String) False))]
   [pair? (And (Arrow Any-Pair True)
               (Arrow (Not Any-Pair) False))]
   [procedure? (And (Arrow Any-Fun True)
                    (Arrow (Not Any-Fun) False))]
   [null? (And (Arrow Null True)
               (Arrow (Not Null) False))]
   ;; unary operators
   ; zero?  not integer? string? pair? procedure?]
   [(zero? 0) Boolean]
   [(zero? 1) Boolean]
   [(zero? "0") #:fail]
   [(zero? unbound) #:fail]
   [#:env ((∈ x Any)) (zero? x) #:fail]
   ;; null?
   [(null? 0) False]
   [(null? null) True]
   [#:env ((∈ x Any)) (null? x) Boolean]
   [(null? unbound) #:fail]
   ; string-length
   [(string-length "42") NonnegInteger]
   [(string-length unbound) #:fail]
   [#:env ((∈ x String)) (string-length x) NonnegInteger]
   [#:env ((∈ x Any)) (string-length x) #:fail]
   [#:env ((∈ x (Or Integer String))) (string-length x) #:fail]
   ; not
   [(not "42") False]
   [(not #false) True]
   [(not (not #false)) False]
   [#:env ((∈ x Any)) (not x) Boolean]
   [#:env ((∈ x Any)) (not (not x)) Boolean]
   [(not unbound) #:fail]
   ; integer?
   [(exact-integer? "42") False]
   [(exact-integer? exact-integer?) False]
   [(exact-integer? 42) True]
   [#:env ((∈ x (Or Integer String))) (exact-integer? x) Boolean]
   [(exact-integer? unbound) #:fail]
   ; string?
   [(string? "42") True]
   [(string? string?) False]
   [(string? 42) False]
   [#:env ((∈ x (Or Integer String))) (string? x) Boolean]
   [(string? unbound) #:fail]
   ; pair?
   [(pair? "42") False]
   [(pair? pair?) False]
   [(pair? (pair 1 2)) True]
   [#:env ((∈ x (Or Integer String))) (pair? x) False]
   [#:env ((∈ x (Or Integer (Prod Integer String)))) (pair? x) Boolean]
   [(pair? unbound) #:fail]
   ; procedure?
   [(procedure? "42") False]
   [(procedure? procedure?) True]
   [(procedure? (pair 1 2)) False]
   [#:env ((∈ x (Or Integer String))) (procedure? x) False]
   [#:env ((∈ x (Or (Arrow Integer Integer) (Prod Integer String))))
    (procedure? x)
    Boolean]
   [(procedure? unbound) #:fail]
   ;; sqr
   [(sqr 0) Zero]
   [(sqr 1) One]
   [(sqr 3) PosIndex]
   [(sqr "42") #:fail]
   [(sqr unbound) #:fail]
   [(sqr 42.0) NonnegFloat]
   [#:env ((∈ x Zero)) (sqr x) Zero]
   [#:env ((∈ x (Or Zero One)))
    (sqr x)
    (Or Zero One)]
   ;; sqrt
   [(sqr 0) Zero]
   [(sqr 1) One]
   [(sqrt 3) PosReal]
   [(sqrt "42") #:fail]
   [(sqrt unbound) #:fail]
   [(sqrt 42.0) (Or* FloatNaN PosFloatNumber PosFloatInfinity)]
   [#:env ((∈ x Zero)) (sqrt x) Zero]
   [#:env ((∈ x (Or Zero One)))
    (sqrt x)
    (Or Zero One)]
   ;; binary operators
   ;; i.e. + - * / min max < <= =
   [(+ 1 2) PosIndex]
   [(+ (+ 1 2) (+ 1 2)) PosFixnum]
   [(+ (+ 1 2) (* 1 2)) PosFixnum]
   [(+ "1" 2) #:fail]
   [(+ 1 "2") #:fail]
   [(+ 1 unbound) #:fail]
   [(+ unbound 1) #:fail]
   [(- 1 2) Fixnum]
   [(- "1" 2) #:fail]
   [(- 1 "2") #:fail]
   [(- 1 unbound) #:fail]
   [(- unbound 1) #:fail]
   [(* 1 2) PosIndex]
   [(* -1 -2) PosInteger]
   [(* 1 -2) NegInteger]
   [(* "1" 2) #:fail]
   [(* 1 "2") #:fail]
   [(* 1 unbound) #:fail]
   [(* unbound 1) #:fail]
   [(/ 1 2) PosRational]
   [(/ -1 -2) PosRational]
   [(/ 1 -2) NegRational]
   [(/ -2 2) NegRational]
   [(/ "1" 2) #:fail]
   [(/ 1 "2") #:fail]
   [(/ 1 unbound) #:fail]
   [(/ unbound 1) #:fail]
   [(min 1 2) PosByte]
   [(min -1 -2) NegFixnum]
   [(min 1 -2) NegFixnum]
   [(min -2 2) NegFixnum]
   [(min "1" 2) #:fail]
   [(min 1 "2") #:fail]
   [(min 1 unbound) #:fail]
   [(min unbound 1) #:fail]
   [(max 1 2) PosByte]
   [(max -1 -2) NegFixnum]
   [(max 1 -2) PosFixnum]
   [(max -2 2) PosFixnum]
   [(max "1" 2) #:fail]
   [(max 1 "2") #:fail]
   [(max 1 unbound) #:fail]
   [(max unbound 1) #:fail]
   [(< 1 2) True]
   [(< 0 0.0) False]
   [(< -1 -2) Boolean]
   [(< 1 -2) False]
   [(< -2 2) True]
   [(< "1" 2) #:fail]
   [(< 1 "2") #:fail]
   [(< 1 unbound) #:fail]
   [(< unbound 1) #:fail]
   [(<= 1 2) True]
   [(<= 0 0.0) True]
   [(<= -1 -2) Boolean]
   [(<= 1 -2) False]
   [(<= -2 2) True]
   [(<= "1" 2) #:fail]
   [(<= 1 "2") #:fail]
   [(<= 1 unbound) #:fail]
   [(<= unbound 1) #:fail]
   [(= 1 2) False]
   [(= 0 0.0) True]
   [(= -1 -2) Boolean]
   [(= 1 -2) False]
   [(= -2 2) False]
   [(= 42 43) Boolean]
   [(= "1" 2) #:fail]
   [(= 1 "2") #:fail]
   [(= 1 unbound) #:fail]
   [(= unbound 1) #:fail]
   [(expt 1 2) One]
   [(expt 1.2 42) NonnegFloat]
   [(expt -1 -2) Rational]
   [(expt "1" 2) #:fail]
   [(expt 1 "2") #:fail]
   [(expt 1 unbound) #:fail]
   [(expt unbound 1) #:fail]
   [(quotient 1 2) Byte]
   [(quotient 1.2 42) #:fail]
   [(quotient 1 42.1) #:fail]
   [(quotient -1 -2) NonnegInteger]
   [(quotient "1" 2) #:fail]
   [(quotient 1 "2") #:fail]
   [(quotient 1 unbound) #:fail]
   [(quotient unbound 1) #:fail]
   [(modulo 1 1) Zero]
   [(modulo 42 42) Byte]
   [(modulo 1.1 42) #:fail]
   [(modulo 1 42.1) #:fail]
   [(modulo -1 -2) NonposFixnum]
   [(modulo "1" 2) #:fail]
   [(modulo 1 "2") #:fail]
   [(modulo 1 unbound) #:fail]
   [(modulo unbound 1) #:fail]

   
   ;; variable
   [unbound #:fail]
   [#:env ((∈ x Integer))
    x Integer]
   [#:env ((∈ x Integer) (∈ y String))
    x Integer]
   [#:env ((∈ x Integer) (∈ y String))
    y String]
   [#:env ((↝ x y) (∈ y String))
    x String]
   [#:env ((↝ x (projP 1 y)) (∈ y (Prod Integer String)))
    x Integer]
   [#:env ((↝ x (projP 2 y)) (∈ y (Prod Integer String)))
    x String]
   [#:env ((↝ x (projP 2 (projP 1 y))) (∈ y (Prod (Prod Integer String) String)))
    x String]
   [#:env ((∈ x (Not Integer)) (∈ x (Or Integer String)))
    x String]
   [#:env ((∨ (∈ x (Not Integer)) (∈ y (Not Integer))) (∈ y Integer) (∈ x (Or Integer String)))
    x String]

   ;; abstraction
   [(μ (f) (Set (Arrow Integer Integer)) λ (x) (+ x 42)) (Arrow Integer Integer)]
   [(μ (f) (Set (Arrow Integer (Arrow Integer Integer)))
       λ (x) (μ (f) (Set (Arrow Integer Integer))
                λ (y) (+ x y)))
    (Arrow Integer (Arrow Integer Integer))]
   [(μ (f) (Set (Arrow Integer Integer)) λ (x) (+ x "42")) #:fail]
   [#:env ((∈ y Integer))
    (μ (f) (Set (Arrow Integer Integer)) λ (x) (+ x y))
    (Arrow Integer Integer)]
   [(μ (f) (Set (Arrow Integer (Arrow String Integer)))
       λ (x) (μ (f) (Set (Arrow String Integer))
                λ (x) (+ x x))) #:fail]
   [(μ (f) (Set (Arrow Integer Integer) (Arrow String Integer)) λ (x)
       (if (exact-integer? x)
           (+ x 42)
           (string-length x)))
    (And (Arrow Integer Integer) (Arrow String Integer))]
   
   ;; function application (non-predicate)
   [#:env ((∈ x (Or Integer String)))
    (string-length x) #:fail]
   [(string-length "hello world") NonnegInteger]
   [#:env ((∈ x Any))
    (exact-integer? x)
    Boolean]
   [(+ (string-length "1") 2) PosInteger]
   [(+ (string-length 1) 2) #:fail]
   [((μ (f) (Set (Arrow Integer Integer)) λ (x) (+ x 42)) 1) Integer]
   [((μ (f) (Set (Arrow Integer Integer) (Arrow String String)) λ (x) x) 1) Integer]
   [((μ (f) (Set (Arrow Integer Integer) (Arrow String String)) λ (x) x) "1") String]
   [((μ (f) (Set (Arrow Integer Integer) (Arrow String String)) λ (x) x) true) #:fail]
   [(((μ (f) (Set (Arrow Integer (Arrow Integer Integer)))
         λ (x) (μ (f) (Set (Arrow Integer Integer)) λ (y) (+ x y))) 1) 2) Integer]
   [((μ (f) (Set (Arrow Integer Integer)) λ (x) (+ x 42)) "1") #:fail]
   
   ;; pair introduction
   [(pair 1 "2") (Prod One String)]
   [(pair (+ 2 1) "2") (Prod PosIndex String)]
   [(pair (pair 1 2) (pair "1" "2"))
    (Prod (Prod One ByteLargerThanOne) (Prod String String))]
   [(pair (+ 2 "1") "2") #:fail]
   [(pair "2" (+ 2 "1")) #:fail]

   ;; pair projection
   [(proj 1 (pair 1 "2")) One]
   [(proj 2 (pair 1 "2")) String]
   [(string-length (proj 2 (pair 1 "2"))) NonnegInteger]
   [(string-length (proj 1 (pair 1 "2"))) #:fail]
   [(proj 1 "not a pair") #:fail]
   [(proj 2 42) #:fail]
   [(proj 2 unbound) #:fail]

   ;; if
   [#:env ((∈ x Any))
    (if (string? x)
        (string-length x)
        0)
    NonnegInteger]
   [#:env ((∈ x (Or Integer String)))
    (if (string? x)
        (string-length x)
        x)
    Integer]
   [#:env ((∈ x (Or Integer String)))
    (if (exact-integer? x)
        x
        (string-length x))
    Integer]
   [#:env ((∈ x (Or Integer String)))
    (if unbound
        42
        42)
    #:fail]
   [#:env ((∈ x (Or Integer String)))
    (if (exact-integer? x)
        unbound
        (string-length x))
    #:fail]
   [#:env ((∈ x (Or Integer String)))
    (if (exact-integer? x)
        (string-length x)
        unbound)
    #:fail]
   ;; if w/ <
   [#:env ((∈ x Real))
    (if (< 0 x)
        x
        42)
    PosRealNoNaN]
   [#:env ((∈ x Real))
    (if (< 0 x)
        -42
        x)
    NonposReal]
   [#:env ((∈ x Real))
    (if (< x 0)
        x
        -42)
    NegRealNoNaN]
   [#:env ((∈ x Real))
    (if (< x 0)
        42
        x)
    NonnegReal]
   [#:env ((∈ x Real) (∈ y PosReal))
    (if (< y x)
        x
        42)
    PosRealNoNaN]
   ;; if w/ <=
   [#:env ((∈ x Real))
    (if (<= 0 x)
        x
        42)
    NonnegRealNoNaN]
   [#:env ((∈ x Real))
    (if (<= 0 x)
        -42
        x)
    NegReal]
   [#:env ((∈ x Real))
    (if (<= x 0)
        x
        -42)
    NonposRealNoNaN]
   [#:env ((∈ x Real))
    (if (<= x 0)
        42
        x)
    PosReal]
   [#:env ((∈ x Real) (∈ y PosReal))
    (if (<= y x)
        x
        42)
    PosRealNoNaN]
   ;; if w/ =
   [#:env ((∈ x Real))
    (if (= 0 x)
        x
        0.0)
    RealZeroNoNaN]
   [#:env ((∈ x NonnegReal))
    (if (= 0 x)
        42
        x)
    PosReal]
   [#:env ((∈ x NonnegReal))
    (if (= x 0)
        42
        x)
    PosReal]
   [#:env ((∈ x (Or Integer String)))
    (if (string? x)
        x
        (string-length x))
    #:fail]

   ;; let
   [(let (x 42)
      (+ x x))
    PosIndex]
   [#:env ((∈ y Any))
    (let (x y)
      (if (exact-integer? x)
          (+ 1 y)
          42))
    Integer]
   [#:env ((∈ y Any))
    (let (x unbound)
      x)
    #:fail]
   [#:env ((∈ y Any))
    (let (x y)
      (if (exact-integer? x)
          42
          (+ 1 y)))
    #:fail]
   [(let (x 42)
      (let (y 0)
        (+ x y)))
    PosIndex]
   [(let (x 42)
      (let (y "0")
        (+ x y)))
    #:fail]
   [(let (x 42)
      (let (x "0")
        (+ x x)))
    #:fail]
   [#:env ((∈ f (Arrow Any Integer)) (∈ x Integer))
    (if (let (tmp #true)
          (if tmp tmp #false))
        (f x)
        42)
    Integer]
   [#:env ((∈ f (Arrow Any Integer)) (∈ x Any))
    (if (let (tmp #true)
          (if tmp tmp #false))
        (f x)
        42)
    Integer]
   [#:env ((∈ f (Arrow (Or Integer String) Integer)) (∈ x Any))
    (if (let (tmp (exact-integer? x))
          (if tmp tmp (string? x)))
        (f x)
        42)
    Integer]
   [#:env ((∈ f (Arrow (Or Integer (Or False String)) Integer)) (∈ x Any))
    (if (let (tmp (exact-integer? x))
          (if tmp tmp
              (let (tmp (string? x))
                (if tmp tmp (not x)))))
        (f x)
        42)
    Integer]
   [#:env ((∈ x (Or Integer String)) (∈ y Integer))
    (if (exact-integer? x)
        x
        y)
    Integer]
   [#:env ((∈ f (And (Arrow Integer String)
                     (Arrow String False)))
           (∈ x (Or Integer String)))
    (if (f x)
        (+ 1 x)
        (string-length x))
    Integer]
   [#:env ((∈ f (And (Arrow Integer String)
                     (Arrow String False)))
           (∈ x (Or Integer String)))
    (if (f x)
        (string-length x)
        (+ 1 x))
    #:fail]
   [#:env ((∈ f (And (Arrow Integer False)
                     (Arrow String String)))
           (∈ x (Or Integer String)))
    (if (f x)
        (string-length x)
        (+ 1 x))
    Integer]
   [#:env ((∈ f (And (Arrow Integer False)
                     (And (Arrow String String)
                          (Arrow Boolean Empty))))
           (∈ x (Or Integer (Or String Boolean))))
    (if (f x)
        (string-length x)
        (+ 1 x))
    Integer]
   [#:env ((∈ f (And (Arrow Integer False)
                     (And (Arrow String String)
                          (Arrow Boolean Empty))))
           (∈ x (Or Integer (Or String Boolean))))
    (if (f x)
        (+ 1 x)
        (string-length x))
    #:fail]

   ;; a few closures
;   [(closure (VALENV) (μ (f) (Set (Arrow Integer Integer)) λ (x) x))
;    (Arrow Integer Integer)]
;   [(closure (VALENV) (μ (f) (Set (Arrow Integer Integer)) λ(x) (+ y x)))
;    #:fail]
;   [(closure (VALENV [y 42]) (μ (f) (Set (Arrow Integer Integer)) λ(x) (+ y x)))
;    (Arrow Integer Integer)]
;   [(closure (VALENV [y "42"]) (μ (f) (Set (Arrow Integer Integer)) λ(x) (+ y x)))
;    #:fail]
;   [(closure (VALENV [x 1] [y 2]) (μ (f) (Set (Arrow String Integer))
;                                     λ(z) (+ (+ y x) (string-length z))))
;    (Arrow String Integer)]
;   [(closure (VALENV [x 1] [y 2])
;             (μ (f) (Set (Arrow Integer Integer) (Arrow String Integer))
;                λ(z) (if (string? z)
;                         (+ (+ y x)
;                            (string-length z))
;                         (+ (+ y x) z))))
;    (And (Arrow Integer Integer)
;         (Arrow String Integer))]
;   [(closure (VALENV [x 1] [y 2])
;             (μ (f) (Set (Arrow Integer Integer) (Arrow String Integer))
;                λ(z) (if (string? z)
;                         (+ (+ y x) z)
;                         (+ (+ y x)
;                            (string-length z)))))
;    #:fail]

   ;; ICFP 2010 examples
   ;; example 1
   [#:env ((∈ x Any))
    (if (exact-integer? x) (+ 1 x) 0)
    Integer]
   ;; example 2
   [(μ (f) (Set (Arrow (Or String Integer) Integer)) λ (x)
       (if (exact-integer? x)
           (+ 1 x)
           (string-length x)))
    (Arrow (Or String Integer) Integer)]
   ;; example 3
   [#:env ((∈ x (Or False (Prod String String))))
    (if x
        (string-length (proj 1 x))
        -1)
    (Or NonnegInteger NegFixnum)]
   ;; example 4
   [#:env ((∈ x Integer) (∈ f (Arrow (Or Integer String) Integer)))
    (if (ORMACRO (exact-integer? x) (string? x))
        (f x)
        0)
    Integer]
   ;; example 5
   [#:env ((∈ x Any) (∈ y Any))
    (if (ANDMACRO (exact-integer? x) (string? y))
        (+ x (string-length y))
        0)
    Integer]
   ;; example 6
   [#:env ((∈ x (Or Integer String)) (∈ y Any))
    (if (ANDMACRO (exact-integer? x) (string? y))
        (+ x (string-length y))
        (string-length x))
    #:fail]
   ;; example 7
   [#:env ((∈ x Any) (∈ y Any))
    (if (if (exact-integer? x) (string? y) #false)
        (+ x (string-length y))
        0)
    Integer]
   ;; example 8
   [(μ (f) (Set (Arrow (Or String Integer) True)
                (Arrow (Not (Or String Integer)) False))
       λ(x) (ORMACRO (string? x) (exact-integer? x)))
    (And (Arrow (Or String Integer) True)
         (Arrow (Not (Or String Integer)) False))]
   ;; example 9
   [#:env ((∈ x Any) (∈ f (Arrow (Or Integer String) Integer)))
    (if (let (tmp (exact-integer? x))
          (if tmp tmp (string? x)))
        (f x)
        0)
    Integer]
   ;; example 10a
   [#:env ((∈ x Any-Pair))
    (if (exact-integer? (proj 1 x))
        (+ 1 (proj 1 x))
        7)
    Integer]
   ;; example 10b
   [#:env ((∈ x Any-Pair))
    (if (exact-integer? (proj 2 x))
        (+ 1 (proj 2 x))
        7)
    Integer]
   ;; example 11
   [#:env ((∈ g (Arrow (Prod Integer Integer) Integer)))
    (μ (f) (Set (Arrow Any-Pair (Or Integer String)))
       λ(x) (if (ANDMACRO (exact-integer? (proj 1 x))
                          (exact-integer? (proj 2 x)))
                (g x)
                "No"))
    (Arrow Any-Pair (Or Integer String))]
   ;; example 12
   [(μ (f) (Set (Arrow (Prod Integer Any) True)
                (Arrow (Prod (Not Integer) Any) False))
       λ(x) (exact-integer? (proj 1 x)))
    (And (Arrow (Prod Integer Any) True)
         (Arrow (Prod (Not Integer) Any) False))]
   ;; example 13
   [#:env ((∈ x Any) (∈ y Any))
    (CONDMACRO
     [(ANDMACRO (exact-integer? x) (string? y))
      (+ x (string-length y))]
     [(exact-integer? x) (+ 1 x)]
     [else 0])
    Integer]
   ;; example 14
   [#:env ((∈ input (Or Integer String)) (∈ extra Any-Pair))
    (CONDMACRO
     [(ANDMACRO (exact-integer? input) (exact-integer? (proj 1 extra)))
      (+ input (proj 1 extra))]
     [(exact-integer? (proj 1 extra))
      (+ (string-length input) (proj 1 extra))]
     [else 0])
    Integer]


   ;; PADL 2012 examples
   
   ;; abs
   [(μ (f) (Set (Arrow Real NonnegReal))
       λ (x) (if (< 0 x)
                 x
                 (* x -1)))
    (Arrow Real NonnegReal)]

   ;; pythagorean
   [(μ (f) (Set (Arrow (Prod Real Real) NonnegReal))
       λ (p) (sqrt (+ (sqr (proj 1 p)) (sqr (proj 2 p)))))
    (Arrow (Prod Real Real) NonnegReal)]

   ;;nat->hex
   [(μ (nat->hex) (Set (Arrow NonnegInteger ByteList))
       λ (n) (if (= n 0)
                 null
                 (pair (modulo n 16) (nat->hex (quotient n 16)))))
    (Arrow NonnegInteger ByteList)]

   ;;sum-list (sum-vector from PADL), the recursive sum part
   [(μ (sum-list) (Set (Arrow IntList Integer))
       λ (l) (if (null? l)
                 0
                 (+ (proj 1 l) (sum-list (proj 2 l)))))
    (Arrow IntList Integer)]

   ;; sum-vector testing against an index part
   [#:env ((∈ i NonnegInteger) (∈ n Index) (∈ default Index))
    (if (< i n)
        i
        default)
    Index]

   ;; gen-random (tweaked since we don't have a heap in this model
   ;; and we don't have multi-arg functions per se)
   [(let (gen (μ (f) (Set (Arrow (Prod PosByte
                                       (Prod NonnegInteger
                                             (Prod Float Float)))
                                 Float))
                 λ (args)
                 (let (x (proj 1 args))
                   (let (p (proj 1 (proj 2 args)))
                     (let (lower (proj 1 (proj 2 (proj 2 args))))
                       (let (upper (proj 2 (proj 2 (proj 2 args))))
                         (+ lower (/ (* (- upper lower) x) p))))))))
      (let (p (- (expt 2 31) 1))
        (let (A (expt 7 5))
          (let (x 42)
            (gen (pair x (pair p (pair 1.0 2.0))))))))
    Float]
   
   ))


;                       
;                       
;    ;;;;           ;   
;   ;;   ;          ;   
;   ;      ;;;;   ;;;;; 
;   ;;         ;    ;   
;    ;;;;      ;    ;   
;        ;  ;;;;    ;   
;        ; ;   ;    ;   
;   ;    ; ;   ;    ;   
;    ;;;;   ;;;;    ;;; 
;                       
;                       
;
(define-metafunction sot
  PROP : p ... -> p
  [(PROP) tt]
  [(PROP p) p]
  [(PROP p q ...) (∧ p (PROP q ...))])
(define-syntax (sat-tests stx)
  (syntax-case stx ()
    [(_ . cases)
     (with-syntax
         ([(test ...)
           (for/list ([tst (in-list (syntax->list #'cases))])
             (syntax-case tst ()
               [(([x v] ...) (p ...))
                (syntax/loc tst
                  (test-equal (judgment-holds
                               (sat (VALENV [x v] ...)
                                    (PROP p ...)))
                              #t))]
               [(([x v] ...) (p ...) #:fail)
                (syntax/loc tst
                  (test-equal (judgment-holds
                               (sat (VALENV [x v] ...)
                                    (PROP p ...)))
                              #f))]))])
       (syntax/loc stx
         (begin
           test ...)))]))


(module+ test
  (printf "-----------------------\n")
  (printf "SATISFACTION TESTS ...\n")
  (printf "-----------------------\n")
  (sat-tests
   [() (tt)]
   [([x 42]) (tt)]
   [() (ff) #:fail]
   [([x 42]) ((∈ x Integer))]
   [([x "42"]) ((∈ x String))]
   [([x exact-integer?]) ((∈ x (Arrow Empty Any)))]
   [([x exact-integer?]) ((∈ x (Arrow Integer True)))]
   [([x (closure (VALENV) (μ (f) (Set (Arrow Integer Integer)) λ(x) x))])
    ((∈ x (Arrow Integer Integer)))]
   [([x 42]) ((∈ x (Or String Integer)))]
   [([x 42]) ((∈ x String)) #:fail]
   [([x 42] [y "42"]) ((∈ x Integer) (∈ y String))]
   [([x 42] [y "42"]) ((∈ x (Or String Integer)) (∈ y String))]
   [([x 42] [y "42"]) ((∈ x (Or String Integer)) (∈ y Integer)) #:fail]
   [([x 42] [y "42"]) ((∨ (∈ y Integer) (∈ x (Or String Integer))))]
   [([x 42] [y "42"]) ((∨ (∈ x (Or String Integer)) (∈ y Integer)))]
   [([x 42] [y 42]) ((↝ x y))]
   [([x 42] [y "42"]) ((↝ x y)) #:fail]
   [([x 42] [y (pair 42 43)]) ((↝ x (projP 1 y)))]
   [([x 42] [y (pair 43 42)]) ((↝ x (projP 2 y)))]
   [([x 42] [y (pair 42 43)]) ((↝ x (projP 2 y))) #:fail]
   [([x 43] [y (pair 43 42)]) ((↝ x (projP 2 y))) #:fail]
   [([x 42] [y (pair 43 42)]) ((↝ x (projP 2 y))
                               (∈ y (Prod Integer Integer))
                               (∈ x Integer))]))




;                                     
;                                  ;; 
;                 ;;;             ;   
;                   ;             ;   
;   ;   ;  ;;;;     ;     ;;;   ;;;;; 
;   ;   ;      ;    ;    ;; ;;    ;   
;    ; ;       ;    ;    ;   ;    ;   
;    ; ;    ;;;;    ;    ;   ;    ;   
;    ; ;   ;   ;    ;    ;   ;    ;   
;     ;    ;   ;    ;    ;; ;;    ;   
;     ;     ;;;;     ;;   ;;;     ;   
;                                     
;                                     
;                                     
                            
(define (α-equal? t1 t2)
  (alpha-equivalent? sot t1 t2))

(define initial-evaluation-fuel (for/fold ([n '(Nat 0)])
                               ([_ (in-range 50)])
                       `(Nat 1(PLUS),n)))

(define-syntax (valof-tests stx)
  (syntax-case stx ()
    [(_ . cases)
     (with-syntax
         ([(test ...)
           (for/list ([tst (in-list (syntax->list #'cases))])
             (syntax-case tst ()
               [(([x xv] ...) e #:timeout)
                (syntax/loc tst
                  (test-judgment-holds
                   (valof ,initial-evaluation-fuel
                          (;)
                          (VALENV [x xv] ...)
                          ⊢
                          e
                          ⇓
                          TIMEOUT)))]
               [(([x xv] ...) e #:stuck)
                (syntax/loc tst
                  (test-judgment-holds
                   (valof ,initial-evaluation-fuel
                          (;)
                          (VALENV [x xv] ...)
                          ⊢
                          e
                          ⇓
                          STUCK)))]
               [(([x xv] ...) e #:error)
                (syntax/loc tst
                  (test-judgment-holds
                   (valof ,initial-evaluation-fuel
                          (;)
                          (VALENV [x xv] ...)
                          ⊢
                          e
                          ⇓
                          ERROR)))]
               [(([x xv] ...) e expected)
                (quasisyntax/loc tst
                  (match (judgment-holds
                          (valof ,initial-evaluation-fuel
                                 (;)
                                 (VALENV [x xv] ...)
                                 ⊢
                                 e
                                 ⇓
                                 v)
                          v)
                    [(list actual)
                     #,(syntax/loc tst
                         (test-equal actual (term expected)
                                     #:equiv α-equal?))]
                    [oops #,(syntax/loc tst
                              (test-equal oops (term expected)
                                          #:equiv α-equal?))]))]))])
       (syntax/loc stx
         (begin
           test ...)))]))


(module+ test
  (printf "-----------------------\n")
  (printf "EVALUATION TESTS ...\n")
  (printf "-----------------------\n")
  (valof-tests
   [() 42 42]
   [() "42" "42"]
   [() #true #true]
   [() #false #false]
   [() exact-integer? exact-integer?]
   [() (μ (f) (Set (Arrow Integer Integer)) λ(x) x)
   (closure RhoNull (μ (f) (Set (Arrow Integer Integer)) λ(x) x))]
   [([x 42]) x 42]
   [() (error "oh no!") #:error]
   [() (error 42) #:stuck]
   [() (42 42) #:stuck]
   [() ((error "rator error!") 42) #:error]
   [() (add1 (error "rand error!")) #:error]
   [() ((μ (f) (Set (Arrow Integer Integer)) λ(x) (f x)) 42) #:timeout]
   [() ((μ (f) (Set (Arrow Integer Integer)) λ(x) x) 42) 42]
   [() ((μ (f) (Set (Arrow Integer Integer)) λ(x) 43) 42) 43]
   [() ((μ (f) (Set (Arrow Integer Integer)) λ(x) ((μ (f) (Set (Arrow Integer Integer)) λ(x) x) x)) 42) 42]
   [([z "42"]) ((μ (f) (Set (Arrow Integer String)) λ(x) ((μ (f) (Set (Arrow String String)) λ(x) x) z)) 42) "42"]
   [() ((μ (f) (Set (Arrow Integer Integer)) λ(x) x)
        (error "rand error!"))
       #:error]
   
   ;; unops
   
   ;; add1
   [() (add1 42) 43]
   [() (add1 "0") #:stuck]
   [() (add1 (error "rand error!")) #:error]
   ;; sub1
   [() (sub1 42) 41]
   [() (sub1 "0") #:stuck]
   [() (sub1 (error "rand error!")) #:error]
   ;; abs
   [() (abs 42) 42]
   [() (abs -42) 42]
   [() (abs "0") #:stuck]
   [() (abs (error "rand error!")) #:error]
   ;; zero?
   [() (zero? 42) #false]
   [() (zero? 0) #true]
   [() (zero? "0") #:stuck]
   [() (zero? (error "rand error!")) #:error]
   ;; null?
   [() (null? 42) #false]
   [() (null? null) #true]
   [() (null? unbound) #:stuck]
   [() (null? (error "rand error!")) #:error]
   ;; string-length
   [() (string-length 0) #:stuck]
   [() (string-length "0") 1]
   [() (string-length (error "rand error!")) #:error]
   ;; not
   [() (not "0") #false]
   [() (not #false) #true]
   [() (not (not #false)) #false]
   [() (not (error "rand error!")) #:error]
   ;; integer?
   [() (exact-integer? (not #false)) #false]
   [() (exact-integer? (string-length "42")) #true]
   [() (exact-integer? (error "rand error!")) #:error]
   ;; string?
   [() (string? (not #false)) #false]
   [() (string? "42") #true]
   [() (string? (error "rand error!")) #:error]
   ;; pair?
   [() (pair? (not #false)) #false]
   [() (pair? (pair "42" (pair "42" 42))) #true]
   [() (pair? (error "rand error!")) #:error]
   ;; procedure?
   [() (procedure? (pair "42" (pair "42" 42))) #false]
   [() (procedure? procedure?) #true]
   [() (procedure? (μ (f) (Set (Arrow Integer Integer)) λ(x) x)) #true]
   [() (procedure? (error "rand error!")) #:error]
   ;; error
   [() (error "oh no!") #:error]
   [() (error 42) #:stuck]
   ;; sqr
   [() (sqr 42) ,(expt 42 2)]
   [() (sqr -42) ,(expt -42 2)]
   [() (sqr "0") #:stuck]
   [() (sqr (error "rand error!")) #:error]
   
   ;; sqrt
   [() (sqrt 42) ,(sqrt 42)]
   [() (sqrt -42) ,(sqrt -42)]
   [() (sqrt "0") #:stuck]
   [() (sqrt (error "rand error!")) #:error]
   
   ;; binops
   ;; +
   [() (+ 1 2) 3]
   [() (+ "1" 2) #:stuck]
   [() (+ 2 "1") #:stuck]
   [() (+ (error "oh no!") 2) #:error]
   [() (+ 2 (error "oh no!")) #:error]
   [([x 1]) (+ 1 x) 2]
   [([x 42] [y 1]) x 42]
   [([x 42] [y 1]) y 1]
   [([x 42] [y 1]) (+ x y) 43]
   [([x 2] [y 0+1i]) (+ x y) 2+1i]
   ;; -
   [([x 42] [y 1]) (- x y) 41]
   [() (- "1" 2) #:stuck]
   [() (- 2 "1") #:stuck]
   [() (- (error "oh no!") 2) #:error]
   [() (- 2 (error "oh no!")) #:error]
   [([x 2] [y 0+1i]) (- x y) 2-1i]
   ;; *
   [([x 42] [y 2]) (* x y) 84]
   [() (* "1" 2) #:stuck]
   [() (* 2 "1") #:stuck]
   [() (* (error "oh no!") 2) #:error]
   [() (* 2 (error "oh no!")) #:error]
   [([x 2] [y 0+1i]) (* x y) 0+2i]
   ;; /
   [([x 42] [y 2]) (/ x y) 21]
   [([x 42] [y 0]) (/ x y) #:error]
   [() (/ "1" 2) #:stuck]
   [() (/ 2 "1") #:stuck]
   [() (/ (error "oh no!") 2) #:error]
   [() (/ 2 (error "oh no!")) #:error]
   [([x 2] [y 0+1i]) (/ x y) 0-2i]
   ;; min
   [([x 42] [y 2]) (min x y) 2]
   [() (min "1" 2) #:stuck]
   [() (min 2 "1") #:stuck]
   [() (min (error "oh no!") 2) #:error]
   [() (min 2 (error "oh no!")) #:error]
   [([x 2] [y 0+1i]) (min x y) #:stuck]
   ;; max
   [([x 42] [y 2]) (max x y) 42]
   [() (max "1" 2) #:stuck]
   [() (max 2 "1") #:stuck]
   [() (max (error "oh no!") 2) #:error]
   [() (max 2 (error "oh no!")) #:error]
   [([x 2] [y 0+1i]) (max x y) #:stuck]
   ;; <
   [([x 42] [y 2]) (< x y) #false]
   [([x 2] [y 2]) (< x y) #false]
   [([x 1] [y 2]) (< x y) #true]
   [() (< "1" 2) #:stuck]
   [() (< 2 "1") #:stuck]
   [() (< (error "oh no!") 2) #:error]
   [() (< 2 (error "oh no!")) #:error]
   [([x 2] [y 0+1i]) (< x y) #:stuck]
   ;; <=
   [([x 42] [y 2]) (<= x y) #false]
   [([x 2] [y 2]) (<= x y) #true]
   [([x 1] [y 2]) (<= x y) #true]
   [() (<= "1" 2) #:stuck]
   [() (<= 2 "1") #:stuck]
   [() (<= (error "oh no!") 2) #:error]
   [() (<= 2 (error "oh no!")) #:error]
   [([x 2] [y 0+1i]) (<= x y) #:stuck]
   ;; =
   [([x 42] [y 2]) (= x y) #false]
   [([x 2] [y 2]) (= x y) #true]
   [([x 1] [y 2]) (= x y) #false]
   [() (= "1" 2) #:stuck]
   [() (= 2 "1") #:stuck]
   [() (= (error "oh no!") 2) #:error]
   [() (= 2 (error "oh no!")) #:error]
   [([x 2] [y 0+1i]) (= x y) #false]
   ;; expt
   [([x 1] [y 2]) (expt x y) 1]
   [([x +inf.0] [y 0]) (expt x y) 1]
   [([x 42] [y 2]) (expt x y) 1764]
   [() (expt 0 (+ 2 (sqrt -3))) ,(expt 0 (+ 2 (sqrt -3)))]
   [() (expt "1" 2) #:stuck]
   [() (expt 2 "1") #:stuck]
   [() (expt 0 -2) #:error]
   [() (expt 0 (sqrt -1)) #:error]
   [() (expt 0 (- (sqrt -1) 1)) #:error]
   [() (expt (error "oh no!") 2) #:error]
   [() (expt 2 (error "oh no!")) #:error]
   ;; quotient
   [([x 1] [y 2]) (quotient x y) ,(quotient 1 2)]
   [([x 123] [y 3]) (quotient x y) ,(quotient 123 3)]
   [([x 123] [y -3]) (quotient x y) ,(quotient 123 -3)]
   [([x 123] [y 1.0]) (quotient x y) #:stuck]
   [([x 1.23] [y 22]) (quotient x y) #:stuck]
   [([x 123] [y 0]) (quotient (error "oh no!") y) #:error]
   [([x 123] [y 0]) (quotient x (error "oh no!")) #:error]
   ;; modulo
   [([x 1] [y 2]) (modulo x y) ,(modulo 1 2)]
   [([x 123] [y 3]) (modulo x y) ,(modulo 123 3)]
   [([x 123] [y -3]) (modulo x y) ,(modulo 123 -3)]
   [([x 123] [y 1.0]) (modulo x y) #:stuck]
   [([x 1.23] [y 22]) (modulo x y) #:stuck]
   [([x 123] [y 0]) (modulo (error "oh no!") y) #:error]
   [([x 123] [y 0]) (modulo x (error "oh no!")) #:error]
   
   
   ;; closures
   [() (μ (f) (Set (Arrow Integer Integer)) λ(x) x)
       (closure RhoNull (μ (f) (Set (Arrow Integer Integer)) λ(x) x))]
   [([y 42]) (μ (f) (Set (Arrow Integer Integer)) λ(x) (+ x y))
             (closure (RhoSnoc RhoNull[y ↦ 42])
                      (μ (f) (Set (Arrow Integer Integer)) λ(x) (+ x y)))]
   ;; pairs/projections
   [([p (pair 3 4)]) (proj 1 p) 3]
   [([p (pair 3 4)]) (proj 2 p) 4]
   [([p 42]) (proj 1 p) #:stuck]
   [([p 42]) (proj 2 p) #:stuck]
   [() (proj 1 (error "pair")) #:error]
   [() (proj 2 (error "pair")) #:error]
   [() (proj 1 (pair 3 4)) 3]
   [() (proj 1 (pair 3 (+ "1" 4))) #:stuck]
   [() (proj 1 (pair 3 (+ 4 "1"))) #:stuck]
   ;; conditional
   [([x "42"]) (if (string? x) (string-length x) x) 2]
   [([x "42"]) (if (string? x) (string-length x) (add1 "1")) 2]
   [([x 42]) (if (string? x) (string-length x) (add1 x)) 43]
   [([x 42] [y "42"]) (if (+ x y) (string-length x) x) #:stuck]
   [() (if (error "oops") 41 42) #:error]
   [([x "42"]) (if (string? x) (+ 42 x) x) #:stuck]
   [([x "42"]) (if (string? x) (error "unreachable") x) #:error]
   [([x "42"]) (if (string? x) (string-length x) (error "unreachable")) 2]
   [([x 42]) (if (string? x) (string-length x) (error "unreachable"))
             #:error]
   [([x 42]) (if (string? x) (string-length x) (+ x "42"))
             #:stuck]
   [([x 42]) (if (string? x) (string-length x) x) 42]
   [([x "42"]) (if x (string-length x) x) 2]
   [([x 42]) (if (+ "1" x) (string-length x) x) #:stuck]
   [([x 42]) (if x (string-length x) x) #:stuck]
   [([x 42]) (if (string? x) (string-length x) (+ "42" x)) #:stuck]
   ;; local binding
   [([x "42"]) (let (y (string-length x)) y) 2]
   [([x "42"]) (let (y (string-length x)) (+ x y)) #:stuck]
   [([x 42]) (let (y (string-length x)) y) #:stuck]
   [([x "42"]) (let (y (error x)) (+ x y)) #:error]
   [([x "42"]) (let (y 42) (error "oops")) #:error]
   ))


(module+ test
    (test-results))
