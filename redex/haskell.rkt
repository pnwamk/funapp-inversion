#lang racket/base

(require racket/match
         racket/system
         "lang-syntax.rkt")

(provide Inhabited
         Subtype
         Project
         Apply
         Inversion)

(match-define (list in out pid err control)
  (process "numeric-sst pipe"))

(define (Inhabited type)
  (unless (τ? type)
    (error 'Inhabited "not a valid type: ~a" type))
  (define cmd `(Inhabited ,type))
  (writeln cmd out)
  (flush-output out)
  (match (read in)
    [#f #f]
    [#t #t]
    [result (error 'Inhabited
                   "problem talking to Haskell process: ~a did not return ~a, it returned ~a\n"
                   cmd
                   "#true or #false"
                   result)]))

(define (Subtype type1 type2)
  (unless (τ? type1)
    (error 'Subtype "not a valid type: ~a" type1))
  (unless (τ? type2)
    (error 'Subtype "not a valid type: ~a" type2))
  (define cmd `(Subtype ,type1 ,type2))
  (writeln cmd out)
  (flush-output out)
  (match (read in)
    [#f #f]
    [#t #t]
    [result (error 'Subtype
                   "problem talking to Haskell process: ~a did not return ~a, it returned ~a\n"
                   cmd
                   "#true or #false"
                   result)]))

(define (Project index type)
  (unless (or (eqv? index 1) (eqv? index 2))
    (error 'project "not a valid index: ~a" index))
  (unless (τ? type)
    (error 'project "not a valid type: ~a" type))
  (define cmd `(Project ,index ,type))
  (writeln cmd out)
  (flush-output out)
  (match (read in)
    [#f #f]
    [(? τ? result) result]
    [result (error 'Project
                   "problem talking to Haskell process: ~a did not return ~a, it returned ~a\n"
                   cmd
                   "a valid type or #false"
                   result)]))

(define (Apply ftype atype)
  (unless (τ? ftype)
    (error 'Apply "not a valid type: ~a" ftype))
  (unless (τ? atype)
    (error 'Apply "not a valid type: ~a" atype))
  (define cmd `(Apply ,ftype ,atype))
  (writeln cmd out)
  (flush-output out)
  (define result (read in))
  (match result
    [#f #f]
    [(? τ? result) result]
    [result (error 'Apply
                   "problem talking to Haskell process: ~a did not return ~a, it returned ~a\n"
                   cmd
                   "a valid type or #false"
                   result)]))

(define (Inversion ftype atype otype)
  (unless (τ? ftype)
    (error 'Inversion "not a valid type: ~a" ftype))
  (unless (τ? atype)
    (error 'Inversion "not a valid type: ~a" atype))
  (unless (τ? otype)
    (error 'Inversion "not a valid type: ~a" otype))
  (define cmd `(Inversion ,ftype ,atype ,otype))
  (writeln cmd out)
  (flush-output out)
  (define result (read in))
  (match result
    [#f #f]
    [(? τ? result) result]
    [result (error 'Apply
                   "problem talking to Haskell process: ~a did not return ~a, it returned ~a\n"
                   cmd
                   "a valid type or #false"
                   result)]))