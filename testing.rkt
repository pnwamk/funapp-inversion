#lang typed/racket/base

(require "syntactic-type-rep.rkt"
         "semantic-type-rep.rkt"
         "conversion.rkt"
         "semantic-type-ops.rkt"
         "semantic-type-metafunctions.rkt"
         "conversion.rkt"
         (prefix-in semantic: "semantic-numeric-types.rkt")
         (prefix-in syntactic: "syntactic-numeric-types.rkt")
         )


(define add1-semantic
  (->semantic semantic:type-of-add1))
(define +-semantic
  (->semantic semantic:type-of-+))


(: add1-comp-test (-> (Listof Symbol) (Listof NUMERIC) Void))
(define (add1-comp-test names types)
  (for ([name (in-list names)]
        [syntactic-t (in-list types)])
    (eprintf "add1 test for ~a\n" name)
    (define semantic-t (->semantic syntactic-t))
    (define syntactic-result (syntactic-funapp syntactic:type-of-add1 syntactic-t))
    (define semantic-result (funapp add1-semantic semantic-t))
    (cond
      [(not syntactic-result)
       (error 'add1-comp-test "syntactic apply failed, argument type: ~a\n" name)]
      [(not semantic-result)
       (error 'add1-comp-test "semantic apply failed, argument type: ~a\n" name)]
      [(not (subtype? semantic-result (->semantic syntactic-result)))
       (error 'add1-comp-test "semantic </: syntactic result!\n arg: ~a\n semantic: ~a\n syntactic: ~a\n"
              name
              semantic-result
              syntactic-result)])))

(: +-comp-test (-> (Listof Symbol) (Listof NUMERIC) Void))
(define (+-comp-test names types)
  (for ([name1 (in-list names)]
        [syntactic-t1 (in-list types)])
    (for ([name2 (in-list names)]
          [syntactic-t2 (in-list types)])
      (eprintf "+ test for ~a ~a\n" name1 name2)
      (define semantic-t1 (->semantic syntactic-t1))
      (define semantic-t2 (->semantic syntactic-t2))
      (define syntactic-result
        (syntactic-funapp syntactic:type-of-+ syntactic-t1 syntactic-t2))
      (define semantic-result
        (funapp +-semantic (Prod-TYPE semantic-t1 semantic-t2)))
      (cond
        [(not syntactic-result)
         (error '+-comp-test "syntactic apply failed, argument types: ~a ~a\n" name1 name2)]
        [(not semantic-result)
         (error '+-comp-test "semantic apply failed, argument types: ~a ~a\n" name1 name2)]
        [(empty? semantic-result)
         (error '+-comp-test "semantic apply produced Empty, argument types: ~a ~a\n" name1 name2)]
        [(not (subtype? semantic-result (->semantic syntactic-result)))
         (error '+-comp-test "semantic </: syntactic result!\n arg1: ~a\n arg1: ~a\n semantic: ~a\n syntactic: ~a\n"
                name1
                name2
                semantic-result
                syntactic-result)]))))



;; test add1

(add1-comp-test numeric-base-list
                numeric-base-list)
(add1-comp-test (hash-keys numeric-unions-table)
                (hash-values numeric-unions-table))

(+-comp-test numeric-base-list
             numeric-base-list)
(+-comp-test (hash-keys numeric-unions-table)
             (hash-values numeric-unions-table))
