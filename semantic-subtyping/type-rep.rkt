#lang racket/base

(require racket/match
         redex/reduction-semantics
         (only-in racket/set set-union set-intersect set-subtract))


(provide (all-defined-out))

(define-language sot
  ;; base types
  [ι ::= True False Str
     Zero
     One
     Byte-Larger-Than-One
     Positive-Index-Not-Byte
     Positive-Fixnum-Not-Index
     Negative-Fixnum
     Positive-Integer-Not-Fixnum
     Negative-Integer-Not-Fixnum
     Positive-Rational-Not-Integer
     Negative-Rational-Not-Integer
     Float-NaN
     Float-Positive-Zero
     Float-Negative-Zero
     Positive-Float-Number
     Positive-Float-Infinity
     Negative-Float-Number
     Negative-Float-Infinity
     Single-Float-NaN
     Single-Float-Positive-Zero
     Single-Float-Negative-Zero
     Positive-Single-Float-Number
     Positive-Single-Float-Infinity
     Negative-Single-Float-Number
     Negative-Single-Float-Infinity
     Exact-Imaginary
     Exact-Complex
     Float-Imaginary
     Single-Float-Imaginary
     Float-Complex
     Single-Float-Complex]
  ;; types
  [τ σ ::= ι (Pair τ τ) (Fun τ τ) (Or τ τ) (And τ τ) (Not τ) Any Empty]
  ;; misc
  [bool ::= #t #f]
  ;; internal defs
  [prop-or-Env ::= p Γ]
  [e-or-v ::= e v]
  
  ;; TYPE REPRESENTATION GRAMMAR
  ;; - - - - - - - - - - - - - -
  ;; types (efficient representation)
  [t s ::= (Type β Prodb Arrowb)]
  [β ::= (Base bool B)]
  [B ::= (Set ι ...)]
  ;; Lazy Binary Decision Diagrams (BDD)
  [b ::= Top Bot n]
  [n ::= (Node a b b b)]
  [a ::= (Pair t t) (Fun t t)]
  [Prodb  ::= Top Bot (Node (Pair t t) Prodb Prodb Prodb)]
  [Arrowb ::= Top Bot (Node (Fun t t) Arrowb Arrowb Arrowb)]
  ;; Base type union/negation
  [P N ::= ∅ (set-cons a P)])


(define-term Bool (Or True False))
(define-term Any-Pair (Pair Any Any))
(define-term Any-Fun  (Fun Empty Any))
(define-term Any-Base (Not (Or Any-Pair Any-Fun)))

(define-judgment-form sot
  #:mode (equal-to I I)
  #:contract (equal-to any any)
  [------------------
   (equal-to any_1 any_1)])


;; an ordering on symbol/null/cons trees
;; #t < #f < sym < nil < cons
(define (raw-term<? t1 t2)
  (match* (t1 t2)
    [(_ _)
     #:when (eq? t1 t2)
     #f]
    [(_ #t) #f]
    [(#t _) #t]
    [(_ #f) #f]
    [(#f _) #t]
    [((? symbol? x) (? symbol? y))
     (symbol<? x y)]
    [((? symbol? x) _) #t]
    [((list) _) #t]
    [((cons x xs) (cons y ys))
     (cond
       [(raw-term<? x y) #t]
       [(raw-term<? y x) #f]
       [else (raw-term<? xs ys)])]
    [((cons _ _) _) #f]))


(define-judgment-form sot
  #:mode (less-than I I)
  #:contract (less-than any any)
  [(where #t ,(raw-term<? (term any_1) (term any_2)))
   -----------------------
   (less-than any_1 any_2) ])

(define-judgment-form sot
  #:mode (greater-than I I)
  #:contract (greater-than any any)
  [(less-than any_2 any_1)
   -----------------------
   (greater-than any_1 any_2)])


(define-metafunction sot
  Base-t : ι -> t
  [(Base-t ι) (Type (Base #t (Set ι)) Bot Bot)])

(define-metafunction sot
  Prod-t : t t -> t
  [(Prod-t t_1 t_2) (Type (Base #t (Set)) (Node (Pair t_1 t_2) Top Bot Bot) Bot)])

(define-metafunction sot
  Arrow-t : t t -> t
  [(Arrow-t t_1 t_2) (Type (Base #t (Set)) Bot (Node (Fun t_1 t_2) Top Bot Bot))])


(define-metafunction sot
  parse : τ -> t
  [(parse ι) (Type (Base #t (Set ι)) Bot Bot)]
  [(parse (Pair τ σ)) (Type (Base #t (Set)) (Node (Pair t s) Top Bot Bot) Bot)
                      (where t (parse τ))
                      (where s (parse σ))]
  [(parse (Fun τ σ)) (Type (Base #t (Set)) Bot (Node (Fun t s) Top Bot Bot))
                     (where t (parse τ))
                     (where s (parse σ))]
  [(parse (Or τ σ)) (t-or (parse τ) (parse σ))]
  [(parse (And τ σ)) (t-and (parse τ) (parse σ))]
  [(parse (Not τ)) (t-not (parse τ))]
  [(parse Any) (Type (Base #f (Set)) Top Top)]
  [(parse Empty) (Type (Base #t (Set)) Bot Bot)])

;; TODO TEST THIS!
;; redex-check identity bewteen this and parse?
(define-metafunction sot
  read-back : any -> τ or #f
  [(read-back (Type β Prodb Arrowb))
   (smart-Or (And Any-Base (read-back-base β))
             (smart-Or (And Any-Pair (read-back-prods Prodb))
                       (And Any-Fun (read-back-arrows Arrowb))))]
  [(read-back _) #f])

(define-metafunction sot
  smart-Or : τ τ -> τ
  [(smart-Or Any τ) Any]
  [(smart-Or τ Any) Any]
  [(smart-Or Empty τ) τ]
  [(smart-Or τ Empty) τ]
  [(smart-Or τ_1 τ_2) (Or τ_1 τ_2)])

(define-metafunction sot
  smart-And : τ τ -> τ
  [(smart-And Empty τ) Empty]
  [(smart-And τ Empty) Empty]
  [(smart-And Any τ) τ]
  [(smart-And τ Any) τ]
  [(smart-And τ_1 τ_2) (And τ_1 τ_2)])

(define-metafunction sot
  read-back-base : β -> τ
  [(read-back-base (Base #t (Set))) Empty]
  [(read-back-base (Base #f (Set))) Any]
  [(read-back-base (Base #t (Set ι_0 ι_1 ...)))
   ,(for/fold ([res (term ι_0)])
              ([i (in-list (term (ι_1 ...)))])
      (term (smart-Or ,res ,i)))]
  [(read-back-base (Base #f (Set ι_0 ι_1 ...)))
   (Not ,(for/fold ([res (term ι_0)])
                   ([i (in-list (term (ι_1 ...)))])
           (term (smart-Or ,res ,i))))])

(define-metafunction sot
  read-back-prods : Prodb -> τ
  [(read-back-prods Top) Any]
  [(read-back-prods Bot) Empty]
  [(read-back-prods (Node (Pair t_1 t_2) b_l b_m b_r))
   (smart-Or (smart-And (Pair (read-back t_1)
                              (read-back t_2))
                        (read-back-prods b_l))
             (smart-Or (read-back-prods b_m)
                       (smart-And (Not (Pair (read-back t_1)
                                             (read-back t_2)))
                                  (read-back-prods b_r))))])

(define-metafunction sot
  read-back-arrows : Arrowb -> τ
  [(read-back-arrows Top) Any]
  [(read-back-arrows Bot) Empty]
  [(read-back-arrows (Node (Fun t_1 t_2) b_l b_m b_r))
   (smart-Or (smart-And (Fun (read-back t_1)
                             (read-back t_2))
                        (read-back-arrows b_l))
             (smart-Or (read-back-arrows b_m)
                       (smart-And (Not (Fun (read-back t_1)
                                            (read-back t_2)))
                                  (read-back-arrows b_r))))])


(define-metafunction sot
  Set-union : (Set any ...) (Set any ...) -> (Set any ...)
  [(Set-union (Set any_1 ...) (Set any_2 ...))
   (Set ,@(set-union (term (any_1 ...)) (term (any_2 ...))))])

(define-metafunction sot
  Set-intersect : (Set any ...) (Set any ...) -> (Set any ...)
  [(Set-intersect (Set any_1 ...) (Set any_2 ...))
   (Set ,@(set-intersect (term (any_1 ...)) (term (any_2 ...))))])

(define-metafunction sot
  Set-diff : (Set any ...) (Set any ...) -> (Set any ...)
  [(Set-diff (Set any_1 ...) (Set any_2 ...))
   (Set ,@(set-subtract (term (any_1 ...)) (term (any_2 ...))))])

(define-metafunction sot
  Base-or : β β -> β
  [(Base-or (Base #t B_1) (Base #t B_2))
   (Base #t (Set-union B_1 B_2))]
  [(Base-or (Base #f B_1) (Base #f B_2))
   (Base #f (Set-intersect B_1 B_2))]
  [(Base-or (Base #t B_1) (Base #f B_2))
   (Base #f (Set-diff B_2 B_1))]
  [(Base-or (Base #f B_1) (Base #t B_2))
   (Base #f (Set-diff B_1 B_2))])

(define-metafunction sot
  Base-and : β β -> β
  [(Base-and (Base #t B_1) (Base #t B_2))
   (Base #t (Set-intersect B_1 B_2))]
  [(Base-and (Base #f B_1) (Base #f B_2))
   (Base #f (Set-union B_1 B_2))]
  [(Base-and (Base #t B_1) (Base #f B_2))
   (Base #t (Set-diff B_1 B_2))]
  [(Base-and (Base #f B_1) (Base #t B_2))
   (Base #t (Set-diff B_2 B_1))])

(define-metafunction sot
  Base-diff : β β -> β
  [(Base-diff (Base #t B_1) (Base #t B_2))
   (Base #t (Set-diff B_1 B_2))]
  [(Base-diff (Base #f B_1) (Base #f B_2))
   (Base #t (Set-diff B_2 B_1))]
  [(Base-diff (Base #t B_1) (Base #f B_2))
   (Base #t (Set-intersect B_1 B_2))]
  [(Base-diff (Base #f B_1) (Base #t B_2))
   (Base #f (Set-union B_1 B_2))])

(define-metafunction sot
  node : a b b b -> b
  [(node a b_l Top b_r) Top]
  [(node a b b_m b) (b-or b b_m)]
  [(node a b_l b_m b_r) (Node a b_l b_m b_r)])

(define-metafunction sot
  atom : n -> a
  [(atom (Node a b_l b_m b_r)) a])

(define-metafunction sot
  left : n -> b
  [(left (Node a b_l b_m b_r)) b_l])

(define-metafunction sot
  mid : n -> b
  [(mid (Node a b_l b_m b_r)) b_m])

(define-metafunction sot
  right : n -> b
  [(right (Node a b_l b_m b_r)) b_r])

(define-metafunction sot
  b-or : b b -> b
  [(b-or b b) b]
  [(b-or b Top) Top]
  [(b-or Top b) Top]
  [(b-or b Bot) b]
  [(b-or Bot b) b]
  [(b-or n_1 n_2) (node-or n_1 n_2)])

;; this is defined separately for presentation purposes only
;; i.e. these cases could easily be a part of b-or
(define-metafunction sot
  node-or : n n -> b
  [(node-or n_1 n_2)
   (node (atom n_1) (left n_1) (b-or (mid n_1) n_2) (right n_1))
   (judgment-holds (less-than (atom n_1) (atom n_2)))]
  [(node-or n_1 n_2)
   (node (atom n_2) (left n_2) (b-or (mid n_2) n_1) (right n_2))
   (judgment-holds (greater-than (atom n_1) (atom n_2)))]
  [(node-or n_1 n_2)
   (node (atom n_1) (b-or (left n_1) (left n_2)) (b-or (mid n_1) (mid n_2)) (b-or (right n_1) (right n_2)))])

(define-metafunction sot
  b-and : b b -> b
  [(b-and b b) b]
  [(b-and b Top) b]
  [(b-and Top b) b]
  [(b-and b Bot) Bot]
  [(b-and Bot b) Bot]
  [(b-and n_1 n_2) (node-and n_1 n_2)])

;; this is defined separately for presentation purposes only
;; i.e. these cases could easily be a part of b-and
(define-metafunction sot
  node-and : n n -> b
  [(node-and n_1 n_2)
   (node (atom n_1) (b-and (left n_1) n_2) (b-and (mid n_1) n_2) (b-and (right n_1) n_2))
   (judgment-holds (less-than (atom n_1) (atom n_2)))]
  [(node-and n_1 n_2)
   (node (atom n_2) (b-and n_1 (left n_2)) (b-and n_1 (mid n_2)) (b-and n_1 (right n_2)))
   (judgment-holds (greater-than (atom n_1) (atom n_2)))]
  [(node-and n_1 n_2)
   (node (atom n_1) b_l Bot b_r)
   (where b_l (b-and (b-or (left n_1) (mid n_1)) (b-or (left n_2) (mid n_2))))
   (where b_r (b-and (b-or (right n_1) (mid n_1)) (b-or (right n_2) (mid n_2))))])


(define-metafunction sot
  b-not : b -> b
  [(b-not Top) Bot]
  [(b-not Bot) Top]
  [(b-not (Node a b_1 b_2 Bot))
   (node a Bot (b-not (b-or b_2 b_1)) (b-not b_2))]
  [(b-not (Node a Bot b_2 b_3))
   (node a (b-not b_2) (b-not (b-or b_2 b_3)) Bot)]
  [(b-not (Node a b_1 Bot b_3))
   (node a (b-not b_1) (b-not (b-or b_1 b_3)) (b-not b_3))]
  [(b-not (Node a_1 b_1 b_2 b_3))
   (node a_1 (b-not (b-or b_1 b_2)) Bot (b-not (b-or b_3 b_2)))])


(define-metafunction sot
  b-diff : b b -> b
  [(b-diff b b) Bot]
  [(b-diff b Top) Bot]
  [(b-diff Top b) (b-not b)]
  [(b-diff b Bot) b]
  [(b-diff Bot b) Bot]
  [(b-diff n_1 n_2) (node-diff n_1 n_2)])

;; this is defined separately for presentation purposes only
;; i.e. these cases could easily be a part of b-diff
(define-metafunction sot
  node-diff : n n -> b
  [(node-diff n_1 n_2)
   (node (atom n_1) (b-diff (b-or (left n_1) (mid n_1)) n_2) Bot (b-diff (b-or (right n_1) (mid n_1)) n_2))
   (judgment-holds (less-than (atom n_1) (atom n_2)))]
  [(node-diff n_1 n_2)
   (node (atom n_2) (b-diff n_1 (b-or (left n_2) (mid n_2))) Bot (b-diff n_1 (b-or (right n_2) (mid n_2))))
   (judgment-holds (greater-than (atom n_1) (atom n_2)))]
  [(node-diff n_1 n_2)
   (node (atom n_1) (b-diff (left n_1) n_2) (b-diff (mid n_1) n_2) (b-diff (right n_1) n_2))])

(define-metafunction sot
  t-and : t t -> t
  [(t-and (Type β_1 Prodb_1 Arrowb_1) (Type β_2 Prodb_2 Arrowb_2))
   (Type (Base-and β_1 β_2) (b-and Prodb_1 Prodb_2) (b-and Arrowb_1 Arrowb_2))])

(define-metafunction sot
  t-or : t t -> t
  [(t-or (Type β_1 Prodb_1 Arrowb_1) (Type β_2 Prodb_2 Arrowb_2))
   (Type (Base-or β_1 β_2) (b-or Prodb_1 Prodb_2) (b-or Arrowb_1 Arrowb_2))])

(define-metafunction sot
  t-diff : t t -> t
  [(t-diff (Type β_1 Prodb_1 Arrowb_1) (Type β_2 Prodb_2 Arrowb_2))
   (Type (Base-diff β_1 β_2) (b-diff Prodb_1 Prodb_2) (b-diff Arrowb_1 Arrowb_2))])

(define-metafunction sot
  t-not : t -> t
  [(t-not t) (t-diff Any-t t)])


(define-metafunction sot
  t-or* : t ... -> t
  [(t-or*) Empty-t]
  [(t-or* t) t]
  [(t-or* t s ...) (t-or t (t-or* s ...))])

(define-metafunction sot
  t-and* : t ... -> t
  [(t-and*) Any-t]
  [(t-and* t) t]
  [(t-and* t s ...) (t-and t (t-and* s ...))])



(define-term Any-t (Type (Base #f (Set)) Top Top))
(define-term Empty-t (Type (Base #t (Set)) Bot Bot))
(define-term Any-Prod-t (Type (Base #t (Set)) Top Bot))
(define-term Any-Fun-t (Type (Base #t (Set)) Bot Top))
(define-term Any-Base-t (Type (Base #f (Set)) Bot Bot))
(define-term Str-t (Base-t Str))
(define-term True-t (Base-t True))
(define-term False-t (Base-t False))
(define-term Bool-t (t-or True-t False-t))
(define-term Not-False-t (t-not False-t))