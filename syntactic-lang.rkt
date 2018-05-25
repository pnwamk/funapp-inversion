#lang racket/base

(require redex/reduction-semantics
         racket/match
         racket/set
         racket/list
         "base-lang.rkt")

(provide (all-defined-out)
         (all-from-out "base-lang.rkt"))

(define-extended-language syntactic base
  [btype ::= True False (Or True False) (Or False True)]
  [type ::= ntype btype]
  [uprop ::= tt (∈ 0 type) (∉ 0 type)]
  [cprop ::= tt (∈ 0 type) (∈ 1 type) (∉ 0 type) (∉ 1 type) (∧ (∈ 0 type) (∈ 1 type))]
  [uR ::= (Res type uprop uprop)]
  [uarrow ::= (-> type R)]
  [ucase ::= (ucase-> uarrow uarrow ...)]
  [barrow ::= (-> type type type)]
  [bcase ::= (bcase-> barrow barrow ...)]
  [cR ::= (Res btype cprop cprop)]
  [carrow ::= (-> type type cR)]
  [ccase ::= (ccase-> carrow carrow ...)])

;; roughly the intersection of two types
(define-metafunction syntactic
  restrict : ntype ntype -> ntype
  [(restrict nbase_!_ nbase_!_) (Or)]
  [(restrict nbase nbase) nbase]
  [(restrict nbase (Or any_0 ... nbase any_1 ...)) nbase]
  [(restrict nbase (Or any_0 ...)) (Or)]
  [(restrict (Or any_0 ... nbase any_1 ...) nbase) nbase]
  [(restrict (Or any_0 ...) nbase) (Or)]
  [(restrict (Or nbase_0 ...) (Or nbase_1 ...))
   (Or nbase_2 ...)
   (where (nbase_2 ...) ,(set-intersect (term (nbase_0 ...)) (term (nbase_1 ...))))])


;; roughly type subtraction
(define-metafunction syntactic
  remove : ntype ntype -> ntype
  [(remove nbase nbase) (Or)]
  [(remove nbase_1 nbase_2) nbase_1]
  [(remove nbase_0 (Or nbase_1 ... nbase_0 nbase_2 ...)) (Or)]
  [(remove nbase_0 (Or nbase_1 ...)) nbase_0]
  [(remove (Or nbase_0 ...) nbase_1)
   (Or nbase_2 ...)
   (where (nbase_2 ...) ,(set-remove (term (nbase_0 ...)) (term nbase_1)))]
  [(remove (Or nbase_0 ...) (Or nbase_1 ...))
   (Or nbase_2 ...)
   (where (nbase_2 ...) ,(set-subtract (term (nbase_0 ...)) (term (nbase_1 ...))))])


;; simple subtyping
(define-metafunction syntactic
  nsubtype : ntype ntype -> boolean
  [(nsubtype ntype ntype) #t]
  [(nsubtype (Or nbase_1 ...) ntype)
   ,(for/and ([nb (in-list (term (nbase_1 ...)))])
      (term (nsubtype ,nb ntype)))]
  [(nsubtype ntype (Or nbase_1 ...))
   ,(for/or ([nb (in-list (term (nbase_1 ...)))])
      (term (nsubtype ntype ,nb)))]
  [(nsubtype _ _) #f])

(define-metafunction syntactic
  nequiv : ntype ntype -> boolean
  [(nequiv ntype_1 ntype_2)
   ,(and (term (nsubtype ntype_1 ntype_2))
         (term (nsubtype ntype_2 ntype_1)))])

(define (equiv-types t1 t2)
  (term (nequiv ,t1 ,t2)))







(module+ test
  (require (for-syntax racket/base))
  (define-syntax (test-nequiv stx)
    (syntax-case stx ()
      [(_ t1 t2)
       (syntax/loc #'t1 (test-equal t1 t2 #:equiv equiv-types))]))

  ;; subtyping tests
  (test-equal (term (nsubtype Zero Zero)) #t)
  (test-equal (term (nsubtype Zero One)) #f)
  (test-equal (term (nsubtype Zero (Or Zero One))) #t)
  (test-equal (term (nsubtype (Or Zero One) Zero)) #f)
  (test-equal (term (nsubtype (Or Zero One) (Or One Zero))) #t)
  (test-equal (term (nsubtype (Or Zero One) (Or One Zero Byte-Larger-Than-One))) #t)
  (test-equal (term (nsubtype (Or One Zero Byte-Larger-Than-One) (Or Zero One))) #f)
  
  ;; restrict tests
  (test-nequiv (term (restrict Zero Zero)) (term Zero))
  (test-nequiv (term (restrict Zero One)) (term (Or)))
  (test-nequiv (term (restrict (Or Zero One) One)) (term One))
  (test-nequiv (term (restrict One (Or Zero One))) (term One))
  (test-nequiv (term (restrict (Or Zero One) (Or Zero One))) (term (Or Zero One)))
  (test-nequiv (term (restrict (Or Zero One Byte-Larger-Than-One)
                               (Or Zero One)))
               (term (Or Zero One)))
  (test-nequiv (term (restrict (Or Zero One) (Or Zero One Byte-Larger-Than-One)))
               (term (Or Zero One)))

  ;; remove tests
  (test-nequiv (term (remove Zero Zero)) (term (Or)))
  (test-nequiv (term (remove Zero One)) (term Zero))
  (test-nequiv (term (remove (Or Zero One) One)) (term Zero))
  (test-nequiv (term (remove One (Or Zero One))) (term (Or)))
  (test-nequiv (term (remove (Or Zero One) (Or Zero One))) (term (Or)))
  (test-nequiv (term (remove (Or Zero One Byte-Larger-Than-One)
                             (Or Zero One)))
               (term Byte-Larger-Than-One))
  (test-nequiv (term (remove (Or Zero One) (Or Zero One Byte-Larger-Than-One)))
               (term (Or)))

  (test-results))




