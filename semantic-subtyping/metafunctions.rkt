#lang racket/base

(require redex/reduction-semantics
         racket/match
         (only-in racket/list in-combinations)
         (only-in racket/set set-subtract)
         "type-rep.rkt"
         "inhabitation.rkt")

(provide (all-defined-out))

(define-metafunction sot
  select : i t t -> t
  [(select 1 t_1 t_2) t_1]
  [(select 2 t_1 t_2) t_2])

;; Given a type, calulcate its first
;; projection (or return false if
;; it is not a pair)
(define-metafunction sot
  maybe-project : i t -> t or #f
  [(maybe-project i t)
   (project i Prodb Any-t Any-t ∅)
   (side-condition (term (subtype t Any-Prod-t)))
   (where (Type _ Prodb _) t)]
  [(maybe-project i t) #f])

(define-metafunction sot
  project : i Prodb s s N -> t
  [(project i Bot s_1 s_2 N) Empty-t]
  [(project i Prodb s_1 s_2 N)
   Empty-t
   (side-condition (OR (term (empty s_1)) or (term (empty s_2))))]
  [(project i Top s_1 s_2 N)
   (project-aux i s_1 s_2 N)]
  [(project i (Node (Pair t_1 t_2) Prodb_l Prodb_m Prodb_r) s_1 s_2 N)
   (t-or t_l (t-or t_m t_r))
   (where t_l (project i Prodb_l (t-and s_1 t_1) (t-and s_2 t_2) N))
   (where t_m (project i Prodb_m s_1 s_2 N))
   (where t_r (project i Prodb_r s_1 s_2 (set-cons (Pair t_1 t_2) N)))])

(define-metafunction sot
  project-aux : i s s N -> t
  [(project-aux i s_1 s_2 N)
   Empty-t
   (side-condition (OR (term (empty s_1)) or (term (empty s_2))))]
  [(project-aux i s_1 s_2 ∅) (select i s_1 s_2)]
  [(project-aux i s_1 s_2 (set-cons (Pair t_1 t_2) N))
   (t-or t_l t_r)
   (where t_l (project-aux i (t-diff s_1 t_1) s_2 N))
   (where t_r (project-aux i s_1 (t-diff s_2 t_2) N))])


;; Given a type, calculate its
;; domain (or return #f if it
;; is not a function).
(define-metafunction sot
  maybe-domain : t -> t or #f
  [(maybe-domain t)
   (domain Empty-t Arrowb)
   (side-condition (term (subtype t Any-Fun-t)))
   (where (Type _ _ Arrowb) t)]
  [(maybe-domain t) #f])

;; NOTE slightly diff from haskell
;; version, double check w/ testing of course
(define-metafunction sot
  domain : t Arrowb -> t
  [(domain t Top) t]
  [(domain t Bot) Any-t]
  [(domain t (Node (Fun s_1 s_2) Arrowb_l Arrowb_m Arrowb_r))
   (t-and t_l (t-and t_m t_r))
   (where t_l (domain (t-or t s_1) Arrowb_l))
   (where t_m (domain t Arrowb_m))
   (where t_r (domain t Arrowb_r))])

;; Given a (function) type and
;; a (argument) type, return the
;; type of the result of applying
;; the first to the second, or #f
;; if the first is not a function or
;; if the second is not in the domain
;; of the first.
(define-metafunction sot
  maybe-funapp : t t -> t or #f
  [(maybe-funapp t_f t_a)
   (funapp t_a Any-t Arrowb)
   (where t_d (maybe-domain t_f))
   (side-condition (term (subtype t_a t_d)))
   (where (Type _ _ Arrowb) t_f)]
  [(maybe-funapp t_f t_a) #f])

(define-metafunction sot
  funapp : t t Arrowb -> t
  [(funapp t_a t Bot) Empty-t]
  [(funapp t_a t Arrowb)
   Empty-t
   (side-condition (term (empty t_a)))]
  [(funapp t_a t Top) t]
  [(funapp t_a t (Node (Fun s_1 s_2) Arrowb_l Arrowb_m Arrowb_r))
   (t-or t_l1 (t-or t_l2 (t-or t_m t_r)))
   (where t_l1 (funapp t_a (t-and t s_2) Arrowb_l))
   (where t_l2 (funapp (t-diff t_a s_1) t Arrowb_l))
   (where t_m (funapp t_a t Arrowb_m))
   (where t_r (funapp t_a t Arrowb_r))])


;; TODO description
(define-metafunction sot
  maybe-input-type : t t -> t or #f
  [(maybe-input-type t_f s)
   (input-type Arrowb t_d s ∅)
   (where t_d (maybe-domain t_f))
   (where (Type _ _ Arrowb) t_f)]
  [(maybe-input-type t_f s) #f])

(define-metafunction sot
  input-type : Arrowb t t P -> t
  [(input-type Bot t_d s P) Empty-t]
  [(input-type Top t_d s P)
   (t-diff s_+ s_-)
   (where (Tuple s_+ s_-) (input-type-aux s t_d P))]
  [(input-type (Node (Fun t_1 t_2) Arrowb_l Arrowb_m Arrowb_r) t_d s P)
   (t-or s_l (t-or s_m s_r))
   (where s_l (input-type Arrowb_l t_d s (set-cons (Fun t_1 t_2) P)))
   (where s_m (input-type Arrowb_m t_d s P))
   (where s_r (input-type Arrowb_r t_d s P))])

(define-metafunction sot
  input-type-aux : t t P -> (Tuple t t)
  [(input-type-aux s t_d ∅)
   (Tuple Empty-t t_d)
   (side-condition (term (empty s)))]
  [(input-type-aux s t_d ∅) (Tuple t_d Empty-t)]
  [(input-type-aux s t_d (set-cons (Fun t_1 t_2) P))
   (Tuple (t-or s_1+ s_2+) (t-or s_1- s_2-))
   (where (Tuple s_1+ s_1-) (input-type-aux (t-and s t_2) (t-and t_d t_1) P))
   (where (Tuple s_2+ s_2-) (input-type-aux s t_d P))])

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
;                                  ;;                      
;                   ;             ;                        
;                   ;             ;                        
;  ;;;;;;   ;;;   ;;;;;  ;;;;   ;;;;;  ;   ;  ; ;;    ;;;  
;  ;  ;  ; ;;  ;    ;        ;    ;    ;   ;  ;;  ;  ;   ; 
;  ;  ;  ; ;   ;;   ;        ;    ;    ;   ;  ;   ;  ;     
;  ;  ;  ; ;;;;;;   ;     ;;;;    ;    ;   ;  ;   ;   ;;;  
;  ;  ;  ; ;        ;    ;   ;    ;    ;   ;  ;   ;      ; 
;  ;  ;  ; ;        ;    ;   ;    ;    ;   ;  ;   ;  ;   ; 
;  ;  ;  ;  ;;;;    ;;;   ;;;;    ;     ;;;;  ;   ;   ;;;  
;                                                          
;                                                          
;                                                          


(define (union-domains arrows)
  (for/fold ([dom (term Empty-t)])
            ([a (in-list arrows)])
    (match a
      [`(Fun ,t1 ,_) (term (t-or ,dom ,t1))])))

(define (intersect-domains arrows)
  (for/fold ([dom (term Any-t)])
            ([a (in-list arrows)])
    (match a
      [`(Fun ,t1 ,_) (term (t-and ,dom ,t1))])))

(define (intersect-codomains arrows)
  (for/fold ([cdom (term Any-t)])
            ([a (in-list arrows)])
    (match a
      [`(Fun ,_ ,t2) (term (t-and ,cdom ,t2))])))


(define-metafunction sot
  nmaybe-project : i t -> t or #f
  [(nmaybe-project i t)
   (nproject i Prodb)
   (side-condition (term (subtype t Any-Prod-t)))
   (where (Type _ Prodb _) t)]
  [(nmaybe-project i t) #f])

(define-metafunction sot
  nproject : i Prodb -> t
  [(nproject i Prodb) ,(naive-project (term i) (term Prodb))])

(define (naive-project i bdd)
  (let loop ([bdd bdd]
             [s1 (term Any-t)]
             [s2 (term Any-t)])
    (match bdd
      ['Bot (term Empty-t)]
      ['Top (match* ((term (empty ,s1)) (term (empty ,s2)))
              [(#t _) (term Empty-t)]
              [(_ #t) (term Empty-t)]
              [(#f #f)
               (match i [1 s1] [2 s2])])]
      [`(Node (Pair ,t1 ,t2) ,l ,m ,r)
       (define res1 (loop l
                          (term (t-and ,s1 ,t1))
                          (term (t-and ,s2 ,t2))))
       (define res2 (loop m s1 s2))
       (define res3 (loop r (term (t-diff ,s1 ,t1)) s2))
       (define res4 (loop r s1 (term (t-diff ,s2 ,t2))))
       (term (t-or ,res1 (t-or ,res2 (t-or ,res3 ,res4))))])))


(define-metafunction sot
  nmaybe-domain : t -> t or #f
  [(nmaybe-domain t)
   (ndomain Arrowb)
   (side-condition (term (subtype t Any-Fun-t)))
   (where (Type _ _ Arrowb) t)]
  [(nmaybe-domain t) #f])


(define-metafunction sot
  ndomain : Arrowb -> t
  [(ndomain Arrowb) ,(naive-domain (term Arrowb))])

(define (naive-domain bdd)
  (let loop ([bdd bdd]
             [P '()])
    (match bdd
      ['Bot (term Any-t)]
      ['Top (union-domains P)]
      [`(Node ,a ,l ,m ,r)
       (define res1 (loop l (cons a P)))
       (define res2 (loop m P))
       (define res3 (loop r P))
       (term (t-and ,res1 (t-and ,res2 ,res3)))])))


(define-metafunction sot
  nmaybe-funapp : t t -> t or #f
  [(nmaybe-funapp t_f t_a)
   (nfunapp t_a Arrowb)
   (where t_d (nmaybe-domain t_f))
   (side-condition (term (subtype t_a t_d)))
   (where (Type _ _ Arrowb) t_f)]
  [(nmaybe-funapp t_f t_a) #f])

(define-metafunction sot
  nfunapp : t Arrowb -> t
  [(nfunapp t_a Arrowb) ,(naive-funapp (term t_a) (term Arrowb))])


(define (naive-funapp arg bdd)
  (let loop ([bdd bdd]
             [P '()])
    (match bdd
      ['Bot (term Empty-t)]
      ['Top (for/fold ([res (term Empty-t)])
                      ([P* (in-combinations P)]
                       #:when (not (term (subtype ,arg ,(union-domains
                                                         (set-subtract P P*))))))
              (term (t-or ,res ,(intersect-codomains P*))))]
      [`(Node ,a ,l ,m ,r)
       (define res1 (loop l  (cons a P)))
       (define res2 (loop m P))
       (define res3 (loop r P))
       (term (t-or ,res1 (t-or ,res2 ,res3)))])))


(define-metafunction sot
  nmaybe-input-type : t t -> t or #f
  [(nmaybe-input-type t_f s)
   (t-and t_d (ninput-type s Arrowb))
   (where t_d (maybe-domain t_f))
   (where (Type _ _ Arrowb) t_f)]
  [(nmaybe-input-type t_f s) #f])

(define-metafunction sot
  ninput-type : t Arrowb -> t
  [(ninput-type s Arrowb) ,(naive-input-type (term s) (term Arrowb))])

(define (naive-input-type s bdd)
  (let loop ([bdd bdd]
             [P '()])
    (match bdd
      ['Bot (term Empty-t)]
      ['Top
       (for/fold ([s+ (term Empty-t)]
                  [s- (term Empty-t)]
                  #:result (term (t-diff ,s+ ,s-)))
                 ([P* (in-combinations P)]
                  #:when (not (null? P*)))
         (define dom (intersect-domains P*))
         (match (term (overlap ,s ,(intersect-codomains P*)))
           [#t (values (term (t-or ,s+ ,(intersect-domains P*)))
                       s-)]
           [#f (values s+
                       (term (t-or ,s- ,(intersect-domains P*))))]))]
      [`(Node ,a ,l ,m ,r)
       (define res1 (loop l (cons a P)))
       (define res2 (loop m P))
       (define res3 (loop r P))
       (term (t-or ,res1 (t-or ,res2 ,res3)))])))