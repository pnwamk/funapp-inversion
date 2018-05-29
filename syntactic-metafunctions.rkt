#lang racket/base

(require redex/reduction-semantics
         racket/match
         racket/set
         racket/list
         "base-lang.rkt")

(provide (all-defined-out)
         (all-from-out "base-lang.rkt"))

(define-term Bool (U True False))

(define funtype? (redex-match? base funtype))
(define domain? (redex-match? base domain))
(define range? (redex-match? base range))

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
  nsubtype : ntype ntype -> boolean
  [(nsubtype ntype ntype) #t]
  [(nsubtype (U nbase_1 ...) ntype)
   ,(for/and ([nb (in-list (term (nbase_1 ...)))])
      (term (nsubtype ,nb ntype)))]
  [(nsubtype ntype (U nbase_1 ...))
   ,(for/or ([nb (in-list (term (nbase_1 ...)))])
      (term (nsubtype ntype ,nb)))]
  [(nsubtype _ _) #f])

(define-metafunction base
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




