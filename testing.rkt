#lang racket/base

(require "base-lang.rkt"
         "syntactic-numeric-types.rkt"
         "semantic-numeric-types.rkt"
         "syntactic-metafunctions.rkt"
         "semantic-subtyping/interface.rkt"
         redex/reduction-semantics
         racket/list)

(define add1-syntactic
  (hash-ref syntactic-funtype-table 'add1))
(define add1-semantic
  (term (syntactic->semantic
         ,(hash-ref semantic-funtype-table 'add1))))

(define (add1-comp-test names types)
  (for/and ([name (in-list names)]
            [syntactic-t (in-list types)])
    (eprintf "add1 test for ~a\n" name)
    (define semantic-t
      (term (syntactic->semantic ,syntactic-t)))
    (define syntactic-result (term (syntactic-funapp ,add1-syntactic ,syntactic-t)))
    (define semantic-result (maybe-apply-function add1-semantic semantic-t))
    (cond
      [(not syntactic-result)
       (error 'add1-comp-test "syntactic apply failed, argument type: ~a\n" name)]
      [(not semantic-result)
       (error 'add1-comp-test "semantic apply failed, argument type: ~a\n" name)]
      [(not (semantic-subtype? semantic-result (term (syntactic->semantic ,syntactic-result))))
       (error 'add1-comp-test "semantic </: syntactic result!\n arg: ~a\n semantic: ~a\n syntactic: ~a\n"
              name
              semantic-result
              syntactic-result)]
      [else #t])))

(define +-syntactic
  (hash-ref syntactic-funtype-table '+))
(define +-semantic
  (term (syntactic->semantic
         ,(hash-ref semantic-funtype-table '+))))

(define (+-comp-test names types)
  (for/and ([name1 (in-list names)]
            [syntactic-t1 (in-list types)])
    (for/and ([name2 (in-list names)]
              [syntactic-t2 (in-list types)])
      (eprintf "+ test for ~a ~a\n" name1 name2)
      (define semantic-t1
        (term (syntactic->semantic ,syntactic-t1)))
      (define semantic-t2
        (term (syntactic->semantic ,syntactic-t2)))
      (eprintf "calculating syntactic result...")
      (define syntactic-result
        (term (syntactic-funapp ,+-syntactic ,syntactic-t1 ,syntactic-t2)))
      (eprintf " ~a\n" syntactic-result)
      (eprintf "calculating semantic result...")
      (define semantic-result
        (maybe-apply-function +-semantic (term (Pair ,semantic-t1 ,semantic-t2))))
      (eprintf " ~a\n" semantic-result)
      (cond
        [(not syntactic-result)
         (error '+-comp-test "syntactic apply failed, argument type: ~a ~a\n" name1 name2)]
        [(not semantic-result)
         (error '+-comp-test "semantic apply failed, argument type: ~a ~a\n" name1 name2)]
        [(begin
           (eprintf "comparing results...")
           (not (semantic-subtype? semantic-result (term (syntactic->semantic ,syntactic-result)))))
         (error '+-comp-test "semantic </: syntactic result!\n arg1: ~a\n arg1: ~a\n semantic: ~a\n syntactic: ~a\n"
                name1
                name2
                semantic-result
                syntactic-result)]
        [else
         (eprintf "done\n")
         #t]))))




;; test add1
#;#;
(test-equal (add1-comp-test (hash-keys nbase-type-predicate-table)
                            (hash-keys nbase-type-predicate-table))
            #t)
(test-equal (add1-comp-test (hash-keys numeric-unions-table)
                            (hash-values numeric-unions-table))
            #t)

(test-equal (+-comp-test (hash-keys nbase-type-predicate-table)
                         (hash-keys nbase-type-predicate-table))
            #t)
(test-equal (+-comp-test (hash-keys numeric-unions-table)
                         (hash-values numeric-unions-table))
            #t)

(test-results)
