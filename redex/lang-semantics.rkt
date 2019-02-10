#lang racket/base

(require redex/reduction-semantics
         racket/match
         racket/math
         (rename-in racket [eval racket/base:eval])
         "lang-syntax.rkt"
         "prim-op-types.rkt"
         "haskell.rkt"
         (for-syntax racket/base))

(provide (all-defined-out)
         (all-from-out "prim-op-types.rkt"))

(define nspace (parameterize ((current-namespace (make-base-namespace)))
                 (namespace-require 'racket/math)
                 (current-namespace)))

(define (evaluate expr)
  (racket/base:eval expr nspace))

(define-metafunction sot
  eval : any -> any
  [(eval any) ,(evaluate (term any))])


(define-judgment-form sot
  #:mode (≠ I I)
  #:contract (≠ any any)

  [----------------
   (≠ any_!_1 any_!_1)])


(define-metafunction sot
  δ1 : prim v -> RESULT
  [(δ1 string-length string) (eval (string-length string))]
  [(δ1 not #false) #true]
  [(δ1 not _) #false]
  [(δ1 null? null) #true]
  [(δ1 null? _) #false]
  [(δ1 exact-integer? integer) #true]
  [(δ1 exact-integer? _) #false]
  [(δ1 string? string) #true]
  [(δ1 string? _) #false]
  [(δ1 pair? (pair _ _)) #true]
  [(δ1 pair? _) #false]
  [(δ1 procedure? (closure ρ (μ(f)I λ(x) e))) #true]
  [(δ1 procedure? prim) #true]
  [(δ1 procedure? _) #false]
  [(δ1 error string) ERROR]
  [(δ1 zero? 0) #true]
  [(δ1 zero? integer) #false]
  [(δ1 add1 number) (eval (+ number 1))]
  [(δ1 sub1 number) (eval (- number 1))]
  [(δ1 abs real) (eval (abs real))]
  [(δ1 sqr number) (eval (sqr number))]
  [(δ1 sqrt number) (eval (sqrt number))]
  [(δ1 _ _) STUCK])


(define-metafunction sot
  δ2 : nop2 v v -> RESULT
  [(δ2 + number_1 number_2) (eval (+ number_1 number_2))]
  [(δ2 - number_1 number_2) (eval (- number_1 number_2))]
  [(δ2 * number_1 number_2) (eval (* number_1 number_2))]
  [(δ2 / number_1 0) ERROR]
  [(δ2 / number_1 number_2) (eval (/ number_1 number_2))]
  [(δ2 min real_1 real_2) (eval (min real_1 real_2))]
  [(δ2 max real_1 real_2) (eval (max real_1 real_2))]
  [(δ2 < real_1 real_2) (eval (< real_1 real_2))]
  [(δ2 <= real_1 real_2) (eval (<= real_1 real_2))]
  [(δ2 = number_1 number_2) (eval (= number_1 number_2))]
  [(δ2 expt 0 number)
   (eval (cond
           [(and (real? number) (negative? number)) (quote ERROR)]
           [(real? number) (expt 0 number)]
           [(not (positive? (real-part number))) (quote ERROR)]
           [else (expt 0 number)]))]
  [(δ2 expt number_1 number_2) (eval (expt number_1 number_2))]
  [(δ2 modulo integer 0) ERROR]
  [(δ2 modulo integer_1 integer_2) (eval (modulo integer_1 integer_2))] 
  [(δ2 quotient integer 0) ERROR]
  [(δ2 quotient integer_1 integer_2) (eval (quotient integer_1 integer_2))]
  [(δ2 _ _ _) STUCK])



(define-metafunction sot
  rho-lookup : ρ(path) -> v or STUCK
  [(rho-lookup ρ((projP 1 path)))
   v_1
   (where (pair v_1 v_2) (rho-lookup ρ(path)))]
  [(rho-lookup ρ((projP 2 path)))
   v_2
   (where (pair v_1 v_2) (rho-lookup ρ(path)))]
  [(rho-lookup RhoNull(x)) STUCK]
  [(rho-lookup (RhoSnoc ρ[x_1 ↦ v])(x_1)) v]
  [(rho-lookup (RhoSnoc ρ[x_2 ↦ v])(x_1))
   (rho-lookup ρ(x_1))])

(define-judgment-form sot
  #:mode (val-is-not-a-pair I)
  #:contract (val-is-not-a-pair v)
  [-----------------------
   (val-is-not-a-pair const)]
  [-----------------------
   (val-is-not-a-pair (closure ρ (λ(Set τ_0 τ_1 ...)(x) e)))])

(define-judgment-form sot
  #:mode (const-is-not-a-prim I)
  #:contract (const-is-not-a-prim const)
  [-----------------------
   (const-is-not-a-prim number)]
  [-----------------------
   (const-is-not-a-prim string)]
  [-----------------------
   (const-is-not-a-prim boolean)]
  [-----------------------
   (const-is-not-a-prim null)])



(define-judgment-form sot
  #:mode (valof I I I I I I O)
  #:contract (valof N(;)ρ ⊢ e ⇓ RESULT)


  [----------------- "B-Timeout"
   (valof (Nat 0)(;)ρ ⊢ e ⇓ TIMEOUT)]
  
  [(where RESULT (rho-lookup ρ(x)))
   ---------------------- "B-Var"
   (valof (Nat 1(PLUS)N)(;)ρ ⊢ x ⇓ RESULT)]

  [---------------------- "B-Const"
   (valof (Nat 1(PLUS)N)(;)ρ ⊢ const ⇓ const)]

  [(valof N(;)ρ ⊢ e ⇓ RESULT)
   ---------------------- "B-Ann"
   (valof (Nat 1(PLUS)N)(;)ρ ⊢ (ann e τ) ⇓ RESULT)]
  
  [(valof N(;)ρ ⊢ e_1 ⇓ prim) (valof N(;)ρ ⊢ e_2 ⇓ v_2)
   (where RESULT (δ1 prim v_2))
   ---------------------- "B-AppPrim"
   (valof (Nat 1(PLUS)N)(;)ρ ⊢ (e_1 e_2) ⇓ RESULT)]

  [(valof N(;)ρ ⊢ e_1 ⇓ const) (const-is-not-a-prim const)
   ---------------------- "B-AppFailConst"
   (valof (Nat 1(PLUS)N)(;)ρ ⊢ (e_1 e_2) ⇓ STUCK)]
  
  [(valof N(;)ρ ⊢ e_1 ⇓ FAIL)
   ---------------------- "B-AppFail1"
   (valof (Nat 1(PLUS)N)(;)ρ ⊢ (e_1 e_2) ⇓ FAIL)]

  [(valof N(;)ρ ⊢ e_2 ⇓ FAIL)
   ---------------------- "B-AppFail2"
   (valof (Nat 1(PLUS)N)(;)ρ ⊢ (e_1 e_2) ⇓ FAIL)]

  [(valof N(;)ρ_1 ⊢ e_1 ⇓ (closure ρ_c (μ(f)I λ(x) e_c)))
   (valof N(;)ρ_1 ⊢ e_2 ⇓ v_2)
   (where ρ_2 (RhoSnoc (RhoSnoc ρ_c[x ↦ v_2])[f ↦ (closure ρ_c (μ(f)I λ(x) e_c))]))
   (valof N(;)ρ_2 ⊢ e_c ⇓ RESULT)
   ---------------------- "B-AppClosure"
   (valof (Nat 1(PLUS)N)(;)ρ_1 ⊢ (e_1 e_2) ⇓ RESULT)]

  [(valof N(;)ρ ⊢ e_1 ⇓ v_1)
   (valof N(;)ρ ⊢ e_2 ⇓ v_2)
   (where RESULT (δ2 nop2 v_1 v_2))
   ------------------------- "B-NOp2"
   (valof (Nat 1(PLUS)N)(;)ρ ⊢ (nop2 e_1 e_2) ⇓ RESULT)]

  [(valof N(;)ρ ⊢ e_1 ⇓ FAIL)
   ------------------------- "B-NOp2Fail1"
   (valof (Nat 1(PLUS)N)(;)ρ ⊢ (nop2 e_1 e_2) ⇓ FAIL)]

  [(valof N(;)ρ ⊢ e_2 ⇓ FAIL)
   ------------------------- "B-NOp2Fail2"
   (valof (Nat 1(PLUS)N)(;)ρ ⊢ (nop2 e_1 e_2) ⇓ FAIL)]

  [------------------------- "B-Abs"
   (valof (Nat 1(PLUS)N)(;)ρ ⊢ (μ(f)I λ(x) e_c) ⇓ (closure ρ (μ(f)I λ(x) e_c)))]

  [(valof N(;)ρ ⊢ e ⇓ (pair v_1 v_2))
   (where/hidden v_i ,(match (term i) [1 (term v_1)] [2 (term v_2)]))
   ------------------------- "B-Proj"
   (valof (Nat 1(PLUS)N)(;)ρ ⊢ (proj i e) ⇓ v_i)]

  [(valof N(;)ρ ⊢ e ⇓ v) (val-is-not-a-pair v)
   ------------------------- "B-ProjFail1"
   (valof (Nat 1(PLUS)N)(;)ρ ⊢ (proj i e) ⇓ STUCK)]
  
  [(valof N(;)ρ ⊢ e ⇓ FAIL)
   ------------------------- "B-ProjFail2"
   (valof (Nat 1(PLUS)N)(;)ρ ⊢ (proj i e) ⇓ FAIL)]

  [(valof N(;)ρ ⊢ e_1 ⇓ v_1) (valof N(;)ρ ⊢ e_2 ⇓ v_2)
   ------------------------- "B-Pair"
   (valof (Nat 1(PLUS)N)(;)ρ ⊢ (pair e_1 e_2) ⇓ (pair v_1 v_2))]

  [(valof N(;)ρ ⊢ e_1 ⇓ FAIL)
   ------------------------- "B-PairFail1"
   (valof (Nat 1(PLUS)N)(;)ρ ⊢ (pair e_1 e_2) ⇓ FAIL)]

  [(valof N(;)ρ ⊢ e_2 ⇓ FAIL)
   ------------------------- "B-PairFail2"
   (valof (Nat 1(PLUS)N)(;)ρ ⊢ (pair e_1 e_2) ⇓ FAIL)]

  [(valof N(;)ρ ⊢ e_1 ⇓ v_1) (≠ v_1 #false)
   (valof N(;)ρ ⊢ e_2 ⇓ RESULT)
   ------------------------- "B-IfNonFalse"
   (valof (Nat 1(PLUS)N)(;)ρ ⊢ (if e_1 e_2 e_3) ⇓ RESULT)]

  [(valof N(;)ρ ⊢ e_1 ⇓ #false)
   (valof N(;)ρ ⊢ e_3 ⇓ RESULT)
   ------------------------- "B-IfFalse"
   (valof (Nat 1(PLUS)N)(;)ρ ⊢ (if e_1 e_2 e_3) ⇓ RESULT)]

  [(valof N(;)ρ ⊢ e_1 ⇓ FAIL)
   ------------------------- "B-IfFail"
   (valof (Nat 1(PLUS)N)(;)ρ ⊢ (if e_1 e_2 e_3) ⇓ FAIL)]
  
  [(valof N(;)ρ ⊢ e_1 ⇓ v_1)
   (valof N(;)(RhoSnoc ρ[x ↦ v_1]) ⊢ e_2 ⇓ RESULT)
   -------------------------- "B-Let"
   (valof (Nat 1(PLUS)N)(;)ρ ⊢ (let (x e_1) e_2) ⇓ RESULT)]

  [(valof N(;)ρ ⊢ e_1 ⇓ FAIL)
   -------------------------- "B-LetFail"
   (valof (Nat 1(PLUS)N)(;)ρ ⊢ (let (x e_1) e_2) ⇓ FAIL)])

(define-judgment-form sot
  #:mode (sat I I)
  #:contract (sat ρ p)

  [------------ "M-True"
   (sat ρ tt)]

  [(where v (rho-lookup ρ(path)))
   (check-val ⊢v v : τ)
   ------------ "M-Type"
   (sat ρ (∈ path τ))]

  [(sat ρ p) (sat ρ q)
   ------------ "M-And"
   (sat ρ (∧ p q))]

  [(sat ρ p)
   ------------ "M-Or1"
   (sat ρ (∨ p q))]

  [(sat ρ q)
   ------------ "M-Or2"
   (sat ρ (∨ p q))]

  [(where v (rho-lookup ρ(path_2)))
   (where v (rho-lookup ρ(path_1)))
   ------------ "M-Alias"
   (sat ρ (≡ path_1 path_2))])

(define (index? x) (and (fixnum? x) (>= x 0) (fixnum? (* x 4))))
(define (exact-rational? x) (and (rational? x) (exact? x)))


(define-judgment-form sot
  #:mode (synth-val I I I O)
  #:contract (synth-val ⊢v v : τ)
  [------------------- "TV-Const"
   (synth-val ⊢v const : (const-type const))]
  
  [(synth-val ⊢v v_1 : τ_1) (synth-val ⊢v v_2 : τ_2)
   ------------------- "TV-Pair"
   (synth-val ⊢v (pair v_1 v_2) : (Prod τ_1 τ_2))]

  ;; the declarative version of this type system allows us
  ;; to assign any negative type info s.t. the overall type
  ;; isn't empty (see Frisch et al. 2008),
  ;; which allows us to know that an Int -> Int is also
  ;; _not_ a Str -> Str, etc. Since this redex model is
  ;; a little simplified (i.e. it's algorithmic, it's to
  ;; display clear figures, etc) we secretly just make
  ;; σ Empty which is sound but obviously not complete
  [(where/hidden σ Empty)
   (where τ (And (BigAnd (Arrow τ_1 σ_1) ... (Arrow τ_n σ_n)) (Not σ)))
   (</: τ Empty)
   ---------------------------- "TV-Closure"
   (synth-val ⊢v (closure ρ (μ(f)(Set (Arrow τ_1 σ_1) ... (Arrow τ_n σ_n))λ(x) e)) : τ)]

  [(where/hidden #t #f)
   (synth-val ⊢v v : σ) (where/hidden τ σ) (<: σ τ)
   --------------------
   (synth-val ⊢v v : τ)])

(define-judgment-form sot
  #:mode (check-val I I I I)
  #:contract (check-val ⊢v v : τ)
  [(synth-val ⊢v v : σ) (<: σ τ)
   ---------------
   (check-val ⊢v v : τ)])

(define-judgment-form sot
  #:mode (subres I I I I O)
  #:contract (subres Γ ⊢ R <: R)
  [(where/hidden #t #f)
   (where/hidden τ_2 τ_1) (where/hidden p_2 p_1) (where/hidden q_2 q_1) (where/hidden obj_2 obj_1)
   ;; This rule is allowed and should be rendered,
   ;; but it's not algorithmic and so we have the model
   ;; not use it for our tests with the
   ;; above (where/hidden #t #f).
   (<: τ_1 τ_2) (subobj ⊢ obj_1 <: obj_2)
   (side-condition (proves (EnvSnoc (EnvSnoc Γ p_1) (is obj_1 (And τ_1 (Not False)))) ⊢ p_2))
   (side-condition (proves (EnvSnoc (EnvSnoc Γ q_1) (is obj_1 (And τ_1 False))) ⊢ q_2))
   --------------------- "SR-Sub"
   (subres Γ ⊢ (Res τ_1 p_1 q_1 obj_1) <: (Res τ_2 p_2 q_2 obj_2))]

  [(side-condition (proves (EnvSnoc (EnvSnoc Γ p_1) (is obj_1 (And τ_1 (Not False)))) ⊢ ff))
   (side-condition (proves (EnvSnoc (EnvSnoc Γ q_1) (is obj_1 (And τ_1 False))) ⊢ ff))
   --------------------- "SR-Absurd"
   (subres Γ ⊢ (Res τ_1 p_1 q_1 obj_1) <: (Res Empty ff ff botO))]

  [(side-condition (proves (EnvSnoc (EnvSnoc Γ p_1) (is obj_1 (And τ_1 (Not False)))) ⊢ ff))
   (where/hidden #f (proves (EnvSnoc (EnvSnoc Γ q_1) (is obj_1 (And τ_1 False))) ⊢ ff))
   --------------------- "SR-False"
   (subres Γ ⊢ (Res τ_1 p_1 q_1 obj_1) <: (Res (And τ_1 False) ff q_1 obj_1))]

  [(where/hidden #f (proves (EnvSnoc (EnvSnoc Γ p_1) (is obj_1 (And τ_1 (Not False)))) ⊢ ff))
   (side-condition (proves (EnvSnoc (EnvSnoc Γ q_1) (is obj_1 (And τ_1 False))) ⊢ ff))
   --------------------- "SR-NonFalse"
   (subres Γ ⊢ (Res τ_1 p_1 q_1 obj_1) <: (Res (And τ_1 (Not False)) p_1 ff obj_1))]

  ;; This rule helps make this judgment algorithmic, but is not for rendering.
  [(where/hidden (Res τ_1 p_1 q_1 obj_1) R)
   (where/hidden #f (proves (EnvSnoc (EnvSnoc Γ p_1) (is obj_1 (And τ_1 (Not False)))) ⊢ ff))
   (where/hidden #f (proves (EnvSnoc (EnvSnoc Γ q_1) (is obj_1 (And τ_1 False))) ⊢ ff))
   ------------------------ 
   (subres Γ ⊢ R <: R)]
  )

(define-judgment-form sot
  #:mode (check I I I I I)
  #:contract (check Γ ⊢ e : τ)
  [(synth/sub Γ ⊢ e : (Res σ _ _ _))
   (<: σ τ)
   ----------------------
   (check Γ ⊢ e : τ)])

;; synth/sub synthesizes a type for e in Γ,
;; and then uses subsumption of type results to perform
;; simplifications that help our examples type check.
;; This allows us to not infinite loop trying to use
;; subsumption by being explicit in this implementation
;; about when we actually want to use it.
(define-judgment-form sot
  #:mode (synth/sub I I I I O)
  #:contract (synth/sub Γ ⊢ e : R)

  [(synth Γ ⊢ e : R_1)
   (subres Γ ⊢ R_1 <: R_2)
   -----------------------
   (synth/sub Γ ⊢ e : R_2)])

;; Type synthesis with a simple, automatic subsumption
;; applied where we extend the result with the same
;; proposition we Γ was most recently extended with.
(define-judgment-form sot
  #:mode (synth/ext I I I I O)
  #:contract (synth/ext (EnvSnoc Γ p) ⊢ e : R)
  [(synth/sub (EnvSnoc Γ p) ⊢ e : (Res τ q_+ q_- obj))
   ----------------------
   (synth/ext (EnvSnoc Γ p) ⊢ e : (Res τ (∧ p q_+) (∧ p q_-) obj))])

(define-judgment-form sot
  #:mode (synth/type I I I I O)
  #:contract (synth/type Γ ⊢ e : τ)
  [(synth Γ ⊢ e : (Res τ _ _ _))
   ----------------------
   (synth/type Γ ⊢ e : τ)])


(define-judgment-form sot
  #:mode (rho->Gamma I O)
  #:contract (rho->Gamma ρ Γ)

  [-----------------------
   (rho->Gamma RhoNull EnvNull)]

  [(synth-val ⊢v v_1 : τ_1)
   (rho->Gamma ρ Γ)
   -----------------------
   (rho->Gamma (RhoSnoc ρ(x_1 ↦ v_1)) (EnvSnoc Γ (∈ x_1 τ_1)))])

(define-judgment-form sot
  #:mode (synth I I I I O)
  #:contract (synth Γ ⊢ e : R)

  [(synth/type Γ ⊢ e : τ_1) (<: τ_1 τ_2)
   ---------------------- "T-Ann"
   (synth Γ ⊢ (ann e τ_2) : (Res τ_2 tt tt topO))]

  [---------------------- "T-Const"
   (synth Γ ⊢ const : (const-type-result const))]

  [(lookup-alias Γ ⊢ x ≡ path) (lookup-type Γ ⊢ path ∈ τ)
   ---------------------- "T-Var"
   (synth Γ ⊢ x : (Res τ (is path (Not False)) (is path False) path))]

  [(synth/type Γ ⊢ e_1 : τ_1) (synth Γ ⊢ e_2 : (Res τ_2 _ _ obj_2))
   (fun-sub τ_1 <: τ_2(ARROW)τ) (where (Tuple σ_+ σ_-) (pred-types τ_1 τ_2))
   ---------------------- "T-App"
   (synth Γ ⊢ (e_1 e_2) : (Res τ (is obj_2 σ_+) (is obj_2 σ_-) topO))]
  
  [(where τ_f (nop2-type nop2)) (synth Γ ⊢ e_1 : (Res τ_1 _ _ obj_1)) (synth Γ ⊢ e_2 : (Res τ_2 _ _ obj_2))
   (fun2-sub τ_f <: τ_1(PROD)τ_2(ARROW)τ) (where (Tuple σ_1+ σ_2+ σ_1- σ_2-) (pred2-types τ_f τ_1 τ_2))
   (where p_+ (∧ (is obj_1 σ_1+) (is obj_2 σ_2+))) (where p_- (∧ (is obj_1 σ_1-) (is obj_2 σ_2-)))
   ---------------------- "T-NOp2"
   (synth Γ ⊢ (nop2 e_1 e_2) : (Res τ p_+ p_- topO))]

  [(synth Γ ⊢ e : (Res τ _ _ obj)) (pair-sub τ <: τ_1(PROD)τ_2)
   (where/hidden τ_i ,(match (term i) [1 (term τ_1)] [2 (term τ_2)]))
   ---------------------- "T-Proj"
   (synth Γ ⊢ (proj i e) : (Res τ_i tt tt (obj-proj i obj)))]

  [(synth/type Γ ⊢ e_1 : τ_1) (synth/type Γ ⊢ e_2 : τ_2)
   ---------------------- "T-Pair"
   (synth Γ ⊢ (pair e_1 e_2) : (Res (Prod τ_1 τ_2) tt ff topO))]

  [(where/hidden σ Empty)
   (where τ (And (BigAnd (Arrow τ_1 σ_1) ... (Arrow τ_n σ_n)) (Not σ))) (</: τ Empty)
   (check (EnvSnoc (EnvSnoc Γ (∈ f τ)) (∈ x τ_1)) ⊢ e : σ_1) ... (check (EnvSnoc (EnvSnoc Γ (∈ f τ)) (∈ x τ_n)) ⊢ e : σ_n)
   ---------------------- "T-Abs"
   (synth Γ ⊢ (μ(f)(Set (Arrow τ_1 σ_1) ... (Arrow τ_n σ_n))λ(x) e) : (Res τ tt ff topO))]

  [(synth Γ ⊢ e_1 : (Res τ_1 p_1 q_1 _))
   (synth/ext (EnvSnoc Γ p_1) ⊢ e_2 : R_2) (synth/ext (EnvSnoc Γ q_1) ⊢ e_3 : R_3)
   ---------------------- "T-If"
   (synth Γ ⊢ (if e_1 e_2 e_3) : (ResOr R_2 R_3))]
  
  [(synth Γ ⊢ e_1 : R_1)
   (synth/ext (EnvSnoc Γ (alias-prop x R_1)) ⊢ e_2 : R_2)
   ------------------------ "T-Let"
   (synth Γ ⊢ (let (x e_1) e_2) : R_2)]
  
  ;; this rule illustrates mathematical freedom
  ;; the model is allowed, but for the purposes
  ;; of _running_ the model we don't want to make
  ;; the search space for type checking
  ;; non-deterministic and/or non-algorithmic
  [(where/hidden #t #f)
   (synth Γ ⊢ e : R_1)
   (where/hidden R_2 (Res Any tt tt topO))
   (subres Γ ⊢ R_1 <: R_2)
   ------------------ "T-Sub"
   (synth Γ ⊢ e : R_2)]

  [(where/hidden #t #f)
   (side-condition (proves Γ ⊢ ff))
   ----------------------- "T-ExFalso"
   (synth Γ ⊢ e : (Res Empty ff ff botO))]
  
  )

(define-metafunction sot
  const-type-result : const -> R
  [(const-type-result #false) (Res False ff tt topO)]
  [(const-type-result const) (Res (const-type const) tt ff topO)])

(define numeric-base-predicate-table
  (list
   (cons (λ (n) (eq? n 0))
         'Zero)
   (cons (λ (n) (eq? n 1))
         'One)
   (cons (λ (n) (and (byte? n) (> n 1)))
         'ByteLargerThanOne)
   (cons (λ (x) (and (index? x)
                     (positive? x)
                     (not (byte? x))))
         'PosIndexNotByte)
   (cons (λ (x) (and (fixnum? x)
                     (positive? x)
                     (not (index? x))))
         'PosFixnumNotIndex)
   (cons (λ (x) (and (fixnum? x)
                     (negative? x)))
         'NegFixnum)
   (cons (λ (x) (and (exact-integer? x)
                     (positive? x)
                     (not (fixnum? x))))
         'PosIntegerNotFixnum)
   (cons (λ (x) (and (exact-integer? x)
                     (negative? x)
                     (not (fixnum? x))))
         'NegIntegerNotFixnum)
   (cons (λ (x) (and (exact-rational? x)
                     (positive? x)
                     (not (exact-integer? x))))
         'PosRationalNotInteger)
   (cons (λ (x) (and (exact-rational? x)
                     (negative? x)
                     (not (exact-integer? x))))
         'NegRationalNotInteger)
   (cons (λ (x) (and (flonum? x) (eqv? x +nan.0)))
         'FloatNaN)
   (cons (λ (x) (eqv? x 0.0))
         'FloatPosZero)
   (cons (λ (x) (eqv? x -0.0))
         'FloatNegZero)
   (cons (λ (x) (and (flonum? x) (positive? x) (not (eqv? x +inf.0))))
         'PosFloatNumber)
   (cons (λ (x) (eqv? x +inf.0))
         'PosFloatInfinity)
   (cons (λ (x) (and (flonum? x) (negative? x) (not (eqv? x -inf.0))))
         'NegFloatNumber)
   (cons (λ (x) (eqv? x -inf.0))
         'NegFloatInfinity)
   (cons (λ (x) (and (single-flonum? x) (eqv? x +nan.f)))
         'SingleFloatNaN)
   (cons (λ (x) (eqv? x 0.0f0))
         'SingleFloatPosZero)
   (cons (λ (x) (eqv? x -0.0f0))
         'SingleFloatNegZero)
   (cons (λ (x) (and (single-flonum? x) (positive? x) (not (eqv? x +inf.f))))
         'PosSingleFloatNumber)
   (cons (λ (x) (eqv? x +inf.f))
         'PosSingleFloatInfinity)
   (cons (λ (x) (and (single-flonum? x) (negative? x) (not (eqv? x -inf.f))))
         'NegSingleFloatNumber)
   (cons (λ (x) (eqv? x -inf.f))
         'NegSingleFloatInfinity)
   (cons (λ (x) (and (number? x)
                     (not (real? x))
                     (eqv? 0 (real-part x))
                     (exact? (imag-part x))))
         'ExactImaginary)
   (cons (λ (x) (and (number? x)
                     (not (real? x))
                     (not (eqv? 0 (real-part x)))
                     (exact? (real-part x))
                     (exact? (imag-part x))))
         'ExactComplex)
   (cons (λ (x)
           (and (number? x)
                (flonum? (imag-part x))
                (eqv? 0 (real-part x))))
         'FloatImaginary)
   (cons (λ (x)
           (and (number? x)
                (single-flonum? (imag-part x))
                (eqv? 0 (real-part x))))
         'SingleFloatImaginary)
   (cons (λ (x)
           (and (number? x)
                (flonum? (imag-part x))
                (flonum? (real-part x))))
         'FloatComplex)
   (cons (λ (x)
           (and (number? x)
                (single-flonum? (imag-part x))
                (single-flonum? (real-part x))))
         'SingleFloatComplex)))

(define (lookup-number-type n)
  (or (for/or ([pred/name (in-list numeric-base-predicate-table)])
        (and ((car pred/name) n) (cdr pred/name)))
      (error lookup-number-type "no predicate passed for ~a" n)))


(define-metafunction sot
  int-type : integer -> τ
  [(int-type 0) Zero]
  [(int-type 1) One]
  [(int-type integer)
   ByteLargerThanOne
   (side-condition (term (eval (< 1 integer 256))))]
  [(int-type integer)
   PosIndexNotByte
   (side-condition (term (eval (and (< 255 integer) (fixnum? (* integer 4))))))]
  [(int-type integer)
   PosFixnumNotIndex
   (side-condition (term (eval (and (positive? integer) (fixnum? integer) (not (fixnum? (* integer 4)))))))]
  [(int-type integer)
   NegFixnum
   (side-condition (term (eval (and (negative? integer) (fixnum? integer)))))]
  [(int-type integer)
   PosIntegerNotFixnum
   (side-condition (term (eval (and (positive? integer) (not (fixnum? integer))))))]
  [(int-type integer)
   NegIntegerNotFixnum
   (side-condition (term (eval (and (negative? integer) (not (fixnum? integer))))))])

(define-metafunction sot
  real-type : real -> τ
  [(real-type real)
   PosRationalNotInteger
   (side-condition (term (eval (and (rational? real) (exact? real) (positive? real) (not (exact-integer? real))))))]
  [(real-type real)
   NegRationalNotInteger
   (side-condition (term (eval (and (rational? real) (exact? real) (negative? real) (not (exact-integer? real))))))]
  [(real-type +nan.0) FloatNaN]
  [(real-type 0.0) FloatPosZero]
  [(real-type -0.0) FloatNegZero]
  [(real-type real)
   PosFloatNumber
   (side-condition (term (eval (and (flonum? real) (positive? real) (not (eqv? real +inf.0))))))]
  [(real-type real)
   NegFloatNumber
   (side-condition (term (eval (and (flonum? real) (negative? real) (not (eqv? real -inf.0))))))]
  [(real-type +inf.0) PosFloatInfinity]
  [(real-type -inf.0) NegFloatInfinity]
  [(real-type +nan.f) SingleFloatNaN]
  [(real-type 0.0f0) SingleFloatPosZero]
  [(real-type -0.0f0) SingleFloatNegZero]
  [(real-type real)
   PosSingleFloatNumber
   (side-condition (term (eval (and (single-flonum? real) (positive? real) (not (eqv? real +inf.f))))))]
  [(real-type +inf.f) PosSingleFloatInfinity]
  [(real-type -inf.f) NegSingleFloatInfinity]
  [(real-type real)
   NegSingleFloatNumber
   (side-condition (term (eval (and (single-flonum? real) (negative? real) (not (eqv? real -inf.f))))))])

(define-metafunction sot
  num-type : number -> τ
  [(num-type number)
   ExactImaginary
   (side-condition (term (eval (and (not (real? number)) (eqv? 0 (real-part number)) (exact? (imag-part number))))))]
  [(num-type number)
   ExactComplex
   (side-condition (term (eval (and (not (real? number))
                                    (not (eqv? 0 (real-part number)))
                                    (exact? (real-part number))
                                    (exact? (imag-part number))))))]
  [(num-type number)
   FloatImaginary
   (side-condition (term (eval (and (flonum? (imag-part number)) (eqv? 0 (real-part number))))))]
  [(num-type number)
   SingleFloatImaginary
   (side-condition (term (eval (and (single-flonum? (imag-part number)) (eqv? 0 (real-part number))))))]
  [(num-type number)
   FloatComplex
   (side-condition (term (eval (and (flonum? (imag-part number)) (flonum? (real-part number))))))]
  [(num-type number)
   SingleFloatComplex
   (side-condition (term (eval (and (single-flonum? (imag-part number)) (single-flonum? (real-part number))))))])


(define-metafunction sot
  const-type : const -> τ
  [(const-type integer) (int-type integer)]
  [(const-type real) (real-type real)]
  [(const-type number) (num-type number)]
  [(const-type string) String]
  [(const-type #true) True]
  [(const-type #false) False]
  [(const-type null) Null]
  [(const-type zero?)
   (Arrow Number Boolean)]
  [(const-type string-length)
   (Arrow String NonnegInteger)]
  [(const-type not)
   (And (Arrow False True) (Arrow (Not False) False))]
  [(const-type null?)
   (And (Arrow Null True) (Arrow (Not Null) False))]
  [(const-type exact-integer?)
   (And (Arrow Integer True) (Arrow (Not Integer) False))]
  [(const-type string?)
   (And (Arrow String True) (Arrow (Not String) False))]
  [(const-type pair?)
   (And (Arrow (Prod Any Any) True) (Arrow (Not (Prod Any Any)) False))]
  [(const-type procedure?)
   (And (Arrow (Arrow Empty Any) True) (Arrow (Not (Arrow Empty Any)) False))]
  [(const-type error) (Arrow String Empty)]
  [(const-type nop1) (nop1-type nop1)])


(define-metafunction sot
  ResOr : R R -> R
  [(ResOr (Res τ_1 p_1 q_1 obj_1) (Res τ_2 p_2 q_2 obj_2))
   (Res (Or τ_1 τ_2) (∨ p_1 p_2) (∨ q_1 q_2) (ObjOr obj_1 obj_2))])

(define-metafunction sot
  ObjOr : obj obj -> obj
  [(ObjOr path path) path]
  [(ObjOr botO obj) obj]
  [(ObjOr obj botO) obj]
  [(ObjOr _ _) topO])

(define-judgment-form sot
  #:mode (subobj I I I I)
  #:contract (subobj ⊢ obj <: obj)
  [---------------- "SO-Refl"
   (subobj ⊢ obj <: obj)]
  
  [---------------- "SO-Top"
   (subobj ⊢ obj <: topO)]
  
  [---------------- "SO-Bot"
   (subobj ⊢ botO <: obj)])


(define-judgment-form sot
  #:mode (lookup-alias I I I I O)
  #:contract (lookup-alias Γ ⊢ x ≡ path)

  [(where #f (lookup-alias-helper Γ x))
   ----------------------
   (lookup-alias Γ ⊢ x ≡ x)]
  
  [(where path (lookup-alias-helper Γ x))
   ----------------------
   (lookup-alias Γ ⊢ x ≡ path)])

(define-metafunction sot
  lookup-alias-helper : prop-or-Env x -> path or #f
  [(lookup-alias-helper EnvNull x)
   #f]
  [(lookup-alias-helper (EnvSnoc Γ p) x)
   path
   (where path (lookup-alias-helper p x))]
  [(lookup-alias-helper (EnvSnoc Γ p) x)
   path
   (where path (lookup-alias-helper Γ x))]
  [(lookup-alias-helper (≡ x path) x)
   path]
  [(lookup-alias-helper (∧ p q) x)
   path
   (where path (lookup-alias-helper p x))]
  [(lookup-alias-helper (∧ p q) x)
   path
   (where path (lookup-alias-helper q x))]
  [(lookup-alias-helper _ x)
   #f])


(define-metafunction sot
  is : obj τ -> p
  [(is (projP 1 path) τ) (is path (Prod τ Any))]
  [(is (projP 2 path) τ) (is path (Prod Any τ))]
  [(is _ τ)
   ff
   (judgment-holds (<: τ Empty))]
  [(is x τ) (∈ x τ)]
  [(is topO _) tt]
  [(is botO τ) ff])

(define-judgment-form sot
  #:mode (lookup-type I I I I O)
  #:contract (lookup-type Γ ⊢ path ∈ τ)

  [(where τ (lookup-var-type Γ x))
   -------------------------
   (lookup-type Γ ⊢ x ∈ τ)]

  [(lookup-type Γ ⊢ path ∈ τ)
   (where τ_i (type-proj i τ))
   -------------------------------
   (lookup-type Γ ⊢ (projP i path) ∈ τ_i)])


(define-metafunction sot
  lookup-var-type : Γ x -> τ or #f
  [(lookup-var-type Γ x)
   (get-type ,(hash) Γ x)
   (where #t (has-type? Γ x))]
  [(lookup-var-type Γ x)
   #f
   (where #f (has-type? Γ x))])

(define-metafunction sot
  get-type : any Γ x -> τ
  [(get-type any_hash EnvNull x)
   ,(cond
      [(for/or ([type (in-immutable-hash-values (term any_hash))])
         (judgment-holds (<: ,type Empty)))
       (term Empty)]
      [else
       (hash-ref (term any_hash) (term x) (term Any))])]
  [(get-type any_hash1 (EnvSnoc Γ tt) x)
   (get-type any_hash1 Γ x)]
  [(get-type any_hash1 (EnvSnoc Γ ff) x) Empty]
  [(get-type any_hash1 (EnvSnoc Γ (∧ p q)) x)
   (get-type any_hash1 (EnvSnoc (EnvSnoc Γ q) p) x)]
  [(get-type any_hash1 (EnvSnoc Γ (∨ p q)) x)
   (Or (get-type any_hash1 (EnvSnoc Γ p) x)
       (get-type any_hash1 (EnvSnoc Γ q) x))]
  ;; we should be able to ignore aliases because we're
  ;; never asking for the type of a variable that is just
  ;; an alias for something (i.e. see lookup-type, which
  ;; resolves aliases _then_ calls this function)
  [(get-type any_hash1 (EnvSnoc Γ (≡ _ _)) x)
   (get-type any_hash1 Γ x)]
  [(get-type any_hash1 (EnvSnoc Γ (∈ y τ)) x)
   (get-type any_hash2 Γ x)
   (where any_hash2 ,(hash-update (term any_hash1)
                                  (term y)
                                  (λ (old-t) (if (eq? old-t 'Any)
                                                 (term τ)
                                                 (term (And ,old-t τ))))
                                  (term Any)))])

(define-metafunction sot
  proves : Γ ⊢ p -> boolean
  [(proves Γ ⊢ ff) (absurd-environment ,(hash) Γ)])

(define-metafunction sot
  absurd-environment : any Γ -> boolean
  [(absurd-environment any_hash EnvNull)
   ,(for/or ([type (in-immutable-hash-values (term any_hash))])
      (judgment-holds (<: ,type Empty)))]
  [(absurd-environment any_hash1 (EnvSnoc Γ tt))
   (absurd-environment any_hash1 Γ)]
  [(absurd-environment any_hash1 (EnvSnoc Γ ff)) #t]
  [(absurd-environment any_hash1 (EnvSnoc Γ (∧ p q)))
   (absurd-environment any_hash1 (EnvSnoc (EnvSnoc Γ q) p))]
  [(absurd-environment any_hash1 (EnvSnoc Γ (∨ p q)))
   ,(and (term (absurd-environment any_hash1 (EnvSnoc Γ p)))
         (term (absurd-environment any_hash1 (EnvSnoc Γ q))))]
  ;; we should be able to ignore aliases because we're
  ;; never asking for the type of a variable that is just
  ;; an alias for something (i.e. see lookup-type, which
  ;; resolves aliases _then_ calls this function)
  [(absurd-environment any_hash1 (EnvSnoc Γ (≡ _ _)))
   (absurd-environment any_hash1 Γ)]
  [(absurd-environment any_hash1 (EnvSnoc Γ (∈ y τ)))
   (absurd-environment any_hash2 Γ)
   (where any_hash2 ,(hash-update (term any_hash1)
                                  (term y)
                                  (λ (old-t) (if (eq? old-t 'Any)
                                                 (term τ)
                                                 (term (And ,old-t τ))))
                                  (term Any)))])


;; does x have a type in Γ? (ignores aliasing)
(define-metafunction sot
  has-type? : Γ x -> boolean
  [(has-type? EnvNull x) #f]
  [(has-type? (EnvSnoc _ (∈ x _)) x) #t]
  [(has-type? (EnvSnoc Γ (∧ p q)) x)
   (has-type? (EnvSnoc (EnvSnoc Γ q) p) x)]
  [(has-type? (EnvSnoc Γ (∨ p q)) x)
   ,(and (term (has-type? (EnvSnoc Γ p) x))
         (term (has-type? (EnvSnoc Γ q) x)))]
  [(has-type? (EnvSnoc Γ _) x) (has-type? Γ x)])


(define-metafunction sot
  alias-prop : x R -> p
  [(alias-prop x (Res _ _ _ botO)) ff]
  [(alias-prop x (Res _ _ _ path)) (≡ x path)]
  [(alias-prop x (Res τ p q topO))
   (∧ (∈ x τ) (∨ p_x q_x))
   (where p_x (∧ (∈ x (Not False)) p))
   (where q_x (∧ (∈ x False) q))])



(define-metafunction sot
  type-proj : i τ -> τ or None
  [(type-proj i τ) ,(or (Project (term i) (term τ))
                        'None)])

(define-judgment-form sot
  #:mode (pair-sub I I O I O)
  #:contract (pair-sub τ <: τ(PROD)τ)
  [(where τ_1 ,(Project 1 (term τ)))
   (where τ_2 ,(Project 2 (term τ)))
   ----------------------------
   (pair-sub τ <: τ_1(PROD)τ_2)])

(define-metafunction sot
  obj-proj : i obj -> obj
  [(obj-proj i path) (projP i path)]
  [(obj-proj i topO) topO]
  [(obj-proj i botO) botO])


(define-judgment-form sot
  #:mode (fun-sub I I I I O)
  #:contract (fun-sub τ <: τ(ARROW)τ)
  [(where τ ,(Apply (term τ_1) (term τ_2)))
   ----------------------------
   (fun-sub τ_1 <: τ_2(ARROW)τ)])

(define-judgment-form sot
  #:mode (fun2-sub I I I I I I O)
  #:contract (fun2-sub τ <: τ(PROD)τ(ARROW)τ)
  [(where τ ,(Apply (term τ_f) (term (Prod τ_1 τ_2))))
   ----------------------------
   (fun2-sub τ_f <: τ_1(PROD)τ_2(ARROW)τ)])

(define-metafunction sot
  fun-inv : τ τ τ -> τ or None
  [(fun-inv τ_f τ_a σ) ,(or (Inversion (term τ_f) (term τ_a) (term σ))
                            'None)])

(define-metafunction sot
  pred-types : τ_f τ_a -> (Tuple τ τ) or None
  [(pred-types τ_f τ_a)
   (Tuple σ_+ σ_-)
   (where σ_+ (fun-inv τ_f τ_a (Not False)))
   (where σ_- (fun-inv τ_f τ_a False))]
  [(pred-types τ_f τ_a) None])

(define-metafunction sot
  pred2-types : τ τ τ -> (Tuple τ τ τ τ) or None
  [(pred2-types τ_f τ_1 τ_2)
   (Tuple σ_1+ σ_2+ σ_1- σ_2-)
   (where σ_+ (fun-inv τ_f (Prod τ_1 τ_2) (Not False)))
   (judgment-holds (pair-sub σ_+ <: σ_1+(PROD)σ_2+))
   (where σ_- (fun-inv τ_f (Prod τ_1 τ_2) False))
   (judgment-holds (pair-sub σ_- <: σ_1-(PROD)σ_2-))]
  [(pred2-types τ_f τ_1 τ_2) None])

(define-judgment-form sot
  #:mode (≈ I I)
  #:contract (≈ τ τ)
  [(where #t ,(Subtype (term σ) (term τ)))
   (where #t ,(Subtype (term τ) (term σ)))
   ----------------
   (≈ σ τ)])

(define-judgment-form sot
  #:mode (<: I I)
  #:contract (<: τ τ)
  [(where #t ,(Subtype (term σ) (term τ)))
   ----------------
   (<: σ τ)])

(define-judgment-form sot
  #:mode (</: I I)
  #:contract (</: τ τ)
  [(where #f ,(Subtype (term σ) (term τ)))
   ----------------
   (</: σ τ)])



