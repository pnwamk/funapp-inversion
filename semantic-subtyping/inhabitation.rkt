#lang racket/base

(require "type-rep.rkt"
         redex/reduction-semantics
         racket/match
         (only-in racket/list in-combinations)
         (only-in racket/set set-union set-intersect set-subtract)
         (for-syntax racket/base))

(provide (all-defined-out))

(define-judgment-form sot
  #:mode (<: I I)
  #:contract (<: τ τ)
  [(where #t (subtype (parse σ) (parse τ)))
   ----------------
   (<: σ τ)])

(define-judgment-form sot
  #:mode (≈ I I)
  #:contract (≈ τ τ)
  [(where #t (subtype (parse σ) (parse τ)))
   (where #t (subtype (parse τ) (parse σ)))
   ----------------
   (≈ σ τ)])

(define-metafunction sot
  empty : t -> bool
  [(empty (Type (Base #t (Set)) Prodb Arrowb))
   ,(AND (term (emptyP Prodb Any-t Any-t ∅))
         and (term (emptyA Arrowb Empty-t ∅ ∅)))]
  [(empty _) #f])

(define-metafunction sot
  subtype : t t -> bool
  [(subtype s t) (empty (t-diff s t))])

(define-metafunction sot
  overlap : t t -> bool
  [(overlap s t) (NOT (empty (t-and s t)))])

(define-metafunction sot
  equiv : t t -> bool
  [(equiv s t) ,(AND (term (subtype s t)) and (term (subtype t s)))])

(define-metafunction sot
  NOT : bool -> bool
  [(NOT bool) ,(not (term bool))])

(define-syntax (OR stx)
  (syntax-case stx (or)
    [(_ term1 or term2)
     (syntax/loc stx (or term1 term2))]
    [(_ term1 or term2 or term3)
     (syntax/loc stx (or term1 term2 term3))]))

;; duplicate definition that will be rendered with parens
(define-syntax POR (make-rename-transformer #'OR))

(define-syntax (AND stx)
  (syntax-case stx (and)
    [(_ term1 and term2)
     (syntax/loc stx (and term1 term2))]
    [(_ term1 and term2 and term3)
     (syntax/loc stx (and term1 term2 term3))]))

;; duplicate definition that will be rendered with parens
(define-syntax PAND (make-rename-transformer #'AND))



(define-metafunction sot
  emptyP : Prodb s s N -> bool
  [(emptyP Bot s_1 s_2 N) #t]
  [(emptyP Top s_1 s_2 N)
   ,(OR (term (empty s_1))
        or  (term (empty s_2))
        or  (term (emptyP-aux s_1 s_2 N)))]
  [(emptyP (Node (Pair t_1 t_2) Prodb_l Prodb_m Prodb_r) s_1 s_2 N)
   ,(AND (term (emptyP Prodb_l (t-and s_1 t_1) (t-and s_2 t_2) N))
         and (term (emptyP Prodb_m s_1 s_2 N))
         and (term (emptyP Prodb_r s_1 s_2 (set-cons (Pair t_1 t_2) N))))])


(define-metafunction sot
  emptyP-aux : s s N -> bool
  [(emptyP-aux s_1 s_2 ∅) #f]
  [(emptyP-aux s_1 s_2 (set-cons (Pair t_1 t_2) N))
   ,(AND (POR (term (subtype s_1 t_1)) or  (term (emptyP-aux (t-diff s_1 t_1) s_2 N)))
         and (POR (term (subtype s_2 t_2)) or  (term (emptyP-aux s_1 (t-diff s_2 t_2) N))))])


(define-metafunction sot
  emptyA : Arrowb s P N -> bool
  [(emptyA Bot s P N) #t]
  [(emptyA Top s P ∅) #f]
  [(emptyA Top s P (set-cons (Fun t_1 t_2) N))
   ,(OR (PAND (term (subtype t_1 s)) and  (term (emptyA-aux t_1 (t-not t_2) P)))
        or (term (emptyA Top s P N)))]
  [(emptyA (Node (Fun s_d s_r) Arrowb_l Arrowb_m Arrowb_r) s P N)
   ,(AND (term (emptyA Arrowb_l (t-or s s_d) (set-cons (Fun s_d s_r) P) N))
         and (term (emptyA Arrowb_m s P N))
         and (term (emptyA Arrowb_r s P (set-cons (Fun s_d s_r) N))))])

(define-metafunction sot
  emptyA-aux : t_1 t_2 P -> bool
  [(emptyA-aux t_1 t_2 ∅) ,(OR (term (empty t_1)) or  (term (empty t_2)))]
  [(emptyA-aux t_1 t_2 (set-cons (Fun s_1 s_2) P))
   ,(AND (POR (term (subtype t_1 s_1)) or  (term (emptyA-aux (t-diff t_1 s_1) t_2 P)))
         and (POR (term (subtype t_2 (t-not s_2))) or  (term (emptyA-aux t_1 (t-and t_2 s_2) P))))])





;                                     
;                                     
;                    ;                
;                                     
;   ; ;;   ;;;;    ;;;   ;   ;   ;;;  
;   ;;  ;      ;     ;   ;   ;  ;;  ; 
;   ;   ;      ;     ;    ; ;   ;   ;;
;   ;   ;   ;;;;     ;    ; ;   ;;;;;;
;   ;   ;  ;   ;     ;    ; ;   ;     
;   ;   ;  ;   ;     ;     ;    ;     
;   ;   ;   ;;;;   ;;;;;   ;     ;;;; 
;                                     
;                                     
;                                     
;                                                   
;                 ;                                 
;                 ;        ;                        
;                 ;        ;                        
;    ;;;   ;   ;  ;;;;   ;;;;;  ;   ;  ;;;;    ;;;  
;   ;   ;  ;   ;  ;; ;;    ;    ;   ;  ;; ;;  ;;  ; 
;   ;      ;   ;  ;   ;    ;     ; ;   ;   ;  ;   ;;
;    ;;;   ;   ;  ;   ;    ;     ; ;   ;   ;  ;;;;;;
;       ;  ;   ;  ;   ;    ;     ; ;   ;   ;  ;     
;   ;   ;  ;   ;  ;; ;;    ;     ;;    ;; ;;  ;     
;    ;;;    ;;;;  ;;;;     ;;;    ;    ;;;;    ;;;; 
;                                 ;    ;            
;                                ;     ;            
;                               ;;     ;            
; (for comparison against efficient version)


(define-metafunction sot
  nsubtype : t t -> bool
  [(nsubtype s t) (nempty (t-diff s t))])

(define-metafunction sot
  nempty : t -> bool
  [(nempty (Type (Base #t (Set)) Prodb Arrowb))
   #t
   (where #t ,(naive-empty-prods (term Prodb)))
   (where #t ,(naive-empty-arrows (term Arrowb)))]
  [(nempty _) #f])


(define (naive-empty-prods bdd)
  (let loop ([bdd bdd]
             [s1 (term Any-t)]
             [s2 (term Any-t)]
             [N '()])
    (match bdd
      ['Bot #t]
      ['Top (for/and ([N* (in-combinations N)])
              (or (let ([t1 (term (t-or* ,@(map car N*)))])
                    (term (nsubtype ,s1 ,t1)))
                  (let ([t2c (term (t-or* ,@(map cdr (set-subtract N N*))))])
                    (term (nsubtype ,s2 ,t2c)))))]
      [`(Node (Pair ,t1 ,t2) ,l ,m ,r)
       (and (loop l
                  (term (t-and ,s1 ,t1))
                  (term (t-and ,s2 ,t2))
                  N)
            (loop m s1 s2 N)
            (loop r s1 s2 (cons (cons t1 t2) N)))])))


(define (naive-empty-arrows bdd)
  (let loop ([bdd bdd]
             [dom (term Empty-t)]
             [P '()]
             [N '()])
    (match bdd
      ['Bot #t]
      ['Top (for*/or ([narrow (in-list N)]
                      [t1 (in-value (car narrow))]
                      [t2 (in-value (cdr narrow))]
                      #:when (term (nsubtype ,t1 ,dom)))
              (for/and ([P* (in-combinations P)])
                (or (let ([dom* (term (t-or* ,@(map car (set-subtract P P*))))])
                      (term (nsubtype ,t1 ,dom*)))
                    (let ([rng* (term (t-and* ,@(map cdr P*)))])
                      (term (nsubtype ,rng* ,t2))))))]
      [`(Node (Fun ,t1 ,t2) ,l ,m ,r)
       (and (loop l (term (t-or ,dom ,t1)) (cons (cons t1 t2) P) N)
            (loop m dom P N)
            (loop r dom P (cons (cons t1 t2) N)))])))