#lang racket/base

(require "base-lang.rkt"
         "syntactic-numeric-types.rkt"
         "semantic-numeric-types.rkt"
         "semantic-subtyping/interface.rkt"
         redex/reduction-semantics
         racket/list)

(define add1-syntactic
  (term (syntactic->semantic
         ,(hash-ref syntactic-funtype-table 'add1))))
(define add1-semantic
  (term (syntactic->semantic
         ,(hash-ref semantic-funtype-table 'add1))))

(define (add1-comp-test names types)
  (for/and ([name (in-list names)]
            [raw-t (in-list types)])
    (eprintf "add1 test for ~a\n" name)
    (define t (cond
                [(redex-match? base τ raw-t)
                 raw-t]
                [(redex-match? base syntactic-type raw-t)
                 (term (syntactic->semantic ,raw-t))]
                [else
                 (error 'add1-comp-test
                        "invalid type: ~a\n" raw-t)]))
    (define syntactic-result (maybe-apply-function add1-syntactic t))
    (define semantic-result (maybe-apply-function add1-semantic t))
    (cond
      [(not syntactic-result)
       (error 'add1-comp-test "syntactic apply failed, argument type: ~a\n" name)]
      [(not semantic-result)
       (error 'add1-comp-test "semantic apply failed, argument type: ~a\n" name)]
      [(not (semantic-subtype? semantic-result syntactic-result))
       (error 'add1-comp-test "semantic </: syntactic result!\n arg: ~a\n semantic: ~a\n syntactic: ~a\n"
              name
              semantic-result
              syntactic-result)]
      [else #t])))


(test-equal (add1-comp-test (hash-keys nbase-type-predicate-table)
                            (hash-keys nbase-type-predicate-table))
            #t)
(test-equal (add1-comp-test (hash-keys numeric-unions-table)
                            (hash-values numeric-unions-table))
            #t)

(test-results)
