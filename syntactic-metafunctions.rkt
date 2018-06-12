#lang racket/base

(require redex/reduction-semantics
         racket/match
         racket/set
         racket/list
         "base-lang.rkt")

(provide (all-defined-out)
         (all-from-out "base-lang.rkt"))


;; roughly the intersection of two types
(define-metafunction base
  restrict : ntype ntype -> ntype
  [(restrict nbase_!_ nbase_!_) (Or)]
  [(restrict nbase nbase) nbase]
  [(restrict nbase (U any_0 ... nbase any_1 ...)) nbase]
  [(restrict nbase (U any_0 ...)) (Or)]
  [(restrict (U any_0 ... nbase any_1 ...) nbase) nbase]
  [(restrict (U any_0 ...) nbase) (Or)]
  [(restrict (U nbase_0 ...) (U nbase_1 ...))
   (U nbase_2 ...)
   (where (nbase_2 ...) ,(set-intersect (term (nbase_0 ...)) (term (nbase_1 ...))))])


;; roughly type subtraction
(define-metafunction base
  remove : ntype ntype -> ntype
  [(remove nbase nbase) (Or)]
  [(remove nbase_1 nbase_2) nbase_1]
  [(remove nbase_0 (U nbase_1 ... nbase_0 nbase_2 ...)) (Or)]
  [(remove nbase_0 (U nbase_1 ...)) nbase_0]
  [(remove (U nbase_0 ...) nbase_1)
   (U nbase_2 ...)
   (where (nbase_2 ...) ,(set-remove (term (nbase_0 ...)) (term nbase_1)))]
  [(remove (U nbase_0 ...) (U nbase_1 ...))
   (U nbase_2 ...)
   (where (nbase_2 ...) ,(set-subtract (term (nbase_0 ...)) (term (nbase_1 ...))))])


;; simple subtyping
(define-metafunction base
  syntactic-subtype : ntype ntype -> boolean
  [(syntactic-subtype ntype ntype) #t]
  [(syntactic-subtype nbase_!_ nbase_!_) #f]
  [(syntactic-subtype (U nbase_1 ...) ntype)
   ,(for/and ([nb (in-list (term (nbase_1 ...)))])
      (term (syntactic-subtype ,nb ntype)))]
  [(syntactic-subtype ntype (U nbase_1 ...))
   ,(for/or ([nb (in-list (term (nbase_1 ...)))])
      (term (syntactic-subtype ntype ,nb)))])

(define-metafunction base
  syntactic-funapp : funtype type ... -> type or #f
  ;; none worked
  [(syntactic-funapp (case->) any) #f]
  ;; single argument
  [(syntactic-funapp (case-> (-> (ntype_dom) (ntype_rng)) any ...) ntype_arg)
   ntype_rng
   (side-condition (term (syntactic-subtype ntype_arg ntype_dom)))]
  [(syntactic-funapp (case-> (-> (ntype_dom) (ntype_rng)) any ...) any_arg)
   (syntactic-funapp (case-> any ...) any_arg)]
  ;; two arguments
  [(syntactic-funapp (case-> (-> (ntype_dom1 ntype_dom2) (ntype_rng)) any ...)
                     ntype_arg1 ntype_arg2)
   ntype_rng
   (side-condition (term (syntactic-subtype ntype_arg1 ntype_dom1)))
   (side-condition (term (syntactic-subtype ntype_arg2 ntype_dom2)))]
  [(syntactic-funapp (case-> (-> (ntype_dom1 ntype_dom2) (ntype_rng)) any ...)
                     any_1 any_2)
   (syntactic-funapp (case-> any ...) any_1 any_2)])


(define-metafunction base
  syntactic-equiv : ntype ntype -> boolean
  [(syntactic-equiv ntype_1 ntype_2)
   ,(and (term (syntactic-subtype ntype_1 ntype_2))
         (term (syntactic-subtype ntype_2 ntype_1)))])

(define (equiv-types t1 t2)
  (term (syntactic-equiv ,t1 ,t2)))







(module+ test
  (require (for-syntax racket/base))
  (define-syntax (test-nequiv stx)
    (syntax-case stx ()
      [(_ t1 t2)
       (syntax/loc #'t1 (test-equal t1 t2 #:equiv equiv-types))]))

  ;; subtyping tests
  (test-equal (term (nsubtype Zero Zero)) #t)
  (test-equal (term (nsubtype Zero One)) #f)
  (test-equal (term (nsubtype Zero (U Zero One))) #t)
  (test-equal (term (nsubtype (U Zero One) Zero)) #f)
  (test-equal (term (nsubtype (U Zero One) (U One Zero))) #t)
  (test-equal (term (nsubtype (U Zero One) (U One Zero Byte-Larger-Than-One))) #t)
  (test-equal (term (nsubtype (U One Zero Byte-Larger-Than-One) (U Zero One))) #f)
  
  ;; restrict tests
  (test-nequiv (term (restrict Zero Zero)) (term Zero))
  (test-nequiv (term (restrict Zero One)) (term (Or)))
  (test-nequiv (term (restrict (U Zero One) One)) (term One))
  (test-nequiv (term (restrict One (U Zero One))) (term One))
  (test-nequiv (term (restrict (U Zero One) (U Zero One))) (term (U Zero One)))
  (test-nequiv (term (restrict (U Zero One Byte-Larger-Than-One)
                               (U Zero One)))
               (term (U Zero One)))
  (test-nequiv (term (restrict (U Zero One) (U Zero One Byte-Larger-Than-One)))
               (term (U Zero One)))

  ;; remove tests
  (test-nequiv (term (remove Zero Zero)) (term (Or)))
  (test-nequiv (term (remove Zero One)) (term Zero))
  (test-nequiv (term (remove (U Zero One) One)) (term Zero))
  (test-nequiv (term (remove One (U Zero One))) (term (Or)))
  (test-nequiv (term (remove (U Zero One) (U Zero One))) (term (Or)))
  (test-nequiv (term (remove (U Zero One Byte-Larger-Than-One)
                             (U Zero One)))
               (term Byte-Larger-Than-One))
  (test-nequiv (term (remove (U Zero One) (U Zero One Byte-Larger-Than-One)))
               (term (Or)))

  (test-results))




