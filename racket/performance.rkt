#lang typed/racket/base

(require typed/racket/unsafe)

(provide performance-region)

;; To enable measurement, see the end of this file.

;; The expression form
;;
;;   (performance-region [key-expr ...] body ....)
;;
;; records the time of `body ...` and associated it with
;; the path `(list key-expr ...)`. Times for a path
;; are included in the times for the path's prefixes, but
;; not for any other path. When regions that are nested
;; dynamically, time accumlates only for the most nested
;; region.
;;
;; For example,
;;
;;    (performance-region
;;     ['compile 'module]
;;     (do-expand-module))
;;
;; counts the time for `(do-expand-module)` to '(compile) and
;; to '(compile module), and not to any other path, even if
;; the compilation occurs while expanding another module.
;;
;; The key '_ as a path element is special: it is replaced
;; by the correspondig element of the enclosing region's
;; path (if any).
;;
;; Beware that `body ...` is not in tail position when
;; performance measurement is enabled.

;; ------------------------------------------------------------
;; Re-export this submodule to enable performance measurements

(module performance-regions racket/base
  (provide start-performance-region
           end-performance-region)
  
  (define region-stack #f)
  (define accums (make-hasheq))

  (struct region (path
                  [start #:mutable]        ; start time
                  [start-memory #:mutable] ; memory allocated before start time
                  [as-nested #:mutable]    ; time accumulated for nested regions
                  [as-nested-memory #:mutable])) ; ditto, for memory
  (struct stat ([msecs #:mutable] [memory #:mutable] [count #:mutable]))

  (define stat-key (gensym))

  (define-logger performance)

  (define (start-performance-region . path)
    (set! region-stack (cons (region (if region-stack
                                         ;; Replace '_ elements:
                                         (let loop ([path path]
                                                    [enclosing-path (region-path (car region-stack))])
                                           (if (null? path)
                                               null
                                               (cons (if (and (eq? '_ (car path))
                                                              (pair? enclosing-path))
                                                         (car enclosing-path)
                                                         (car path))
                                                     (loop (cdr path)
                                                           (if (pair? enclosing-path)
                                                               (cdr enclosing-path)
                                                               null)))))
                                         path)
                                     (current-inexact-milliseconds)
                                     (current-memory-use 'cumulative)
                                     0.0
                                     0)
                             region-stack)))
    
  (define (end-performance-region)
    (define now (current-inexact-milliseconds))
    (define now-memory (current-memory-use 'cumulative))
    (define r (car region-stack))
    (set! region-stack (cdr region-stack))

    (define full-delta (- now (region-start r)))
    (define delta (- full-delta (region-as-nested r)))

    (define full-delta-memory (- now-memory (region-start-memory r)))
    (define delta-memory (- full-delta-memory (region-as-nested-memory r)))

    (let loop ([accums accums] [path (region-path r)])
      (define key (car path))
      (let ([accum (or (hash-ref accums key #f)
                       (let ([accum (make-hasheq)])
                         (hash-set! accums key accum)
                         accum))])
        (define s (or (hash-ref accum stat-key #f)
                      (let ([s (stat 0.0 0 0)])
                        (hash-set! accum stat-key s)
                        s)))
        (set-stat-msecs! s (+ delta (stat-msecs s)))
        (set-stat-memory! s (+ delta-memory (stat-memory s)))
        (when (null? (cdr path))
         (set-stat-count! s (add1 (stat-count s))))
        (unless (null? (cdr path))
          (loop accum (cdr path)))))
    
    (when region-stack
      (set-region-as-nested! (car region-stack)
                             (+ (region-as-nested (car region-stack))
                                full-delta))
      (set-region-as-nested-memory! (car region-stack)
                                    (+ (region-as-nested-memory (car region-stack))
                                       full-delta-memory))))
  
  (void (plumber-add-flush! (current-plumber)
                            (lambda (h)
                              (define (whole-len s)
                                (caar (or (regexp-match-positions #rx"[.]" s) '(0))))
                              (define (kb b)
                                (define s (number->string (quotient b 1024)))
                                (list->string
                                 (for/fold ([l null]) ([c (in-list (reverse (string->list s)))]
                                                       [i (in-naturals)])
                                   (cond
                                    [(and (positive? i) (zero? (modulo i 3)))
                                     (list* c #\, l)]
                                    [else (cons c l)]))))
                              (define-values (label-max-len value-max-len memory-max-len count-max-len)
                                (let loop ([accums accums] [label-len 6] [value-len 5] [memory-len 4] [count-len 5] [indent 2])
                                  (for/fold ([label-len label-len]
                                             [value-len value-len]
                                             [memory-len memory-len]
                                             [count-len count-len])
                                            ([(k v) (in-hash accums)])
                                    (cond
                                     [(eq? k stat-key)
                                      (values label-len
                                              (max value-len (whole-len (format "~a" (stat-msecs v))))
                                              (max memory-len (string-length (format "~a" (kb (stat-memory v)))))
                                              (max count-len (string-length (format "~a" (stat-count v)))))]
                                     [else (loop v
                                                 (max label-len (+ indent (string-length (format "~a" k))))
                                                 value-len
                                                 memory-len
                                                 count-len
                                                 (+ 2 indent))]))))
                              (log-performance-info "REGION      ~aMSECS   ~aMEMK   ~aCOUNT"
                                                    (make-string (- (+ label-max-len value-max-len) 11)
                                                                 #\space)
                                                    (make-string (- memory-max-len 4)
                                                                 #\space)
                                                    (make-string (- count-max-len 5)
                                                                 #\space))
                              (let loop ([name #f] [accums accums] [indent ""] [newline? #t])
                                (when name
                                  (define v (hash-ref accums stat-key))
                                  (log-performance-info "~a~a   ~a~a   ~a~a   ~a~a"
                                                        indent
                                                        name
                                                        (make-string (+ (- label-max-len (string-length (format "~a" name)) (string-length indent))
                                                                        (- value-max-len (whole-len (format "~a" (stat-msecs v)))))
                                                                     #\space)
                                                        (regexp-replace #rx"[.](..).*" (format "~a00" (stat-msecs v)) ".\\1")
                                                        (make-string (- memory-max-len (string-length (format "~a" (kb (stat-memory v)))))
                                                                     #\space)
                                                        (kb (stat-memory v))
                                                        (make-string (- count-max-len (string-length (format "~a" (stat-count v))))
                                                                     #\space)
                                                        (stat-count v)))
                                (define keys (sort (for/list ([k (in-hash-keys accums)] #:when (not (eq? k stat-key))) k)
                                                   >
                                                   #:key (lambda (key) (stat-msecs (hash-ref (hash-ref accums key) stat-key)))))
                                (for ([k (in-list keys)]
                                      [i (in-naturals)])
                                  (when (and newline? (positive? i)) (log-performance-info ""))
                                  (loop k (hash-ref accums k) (string-append indent "  ") #f)))))))

;; ------------------------------------------------------------
;; Re-export this submodule to disable measurements


(unsafe-require/typed
 (submod "." performance-regions)
 [start-performance-region
  (->* () () #:rest Symbol Void)]
 [end-performance-region
  (->* () () #:rest Symbol Void)])


;; overhead (i.e. measuring) version:
(define-syntax-rule (performance-region [tag0-expr tag-expr ...] body ...)
  (begin
    (start-performance-region tag0-expr tag-expr ...)
    (begin0
      (let () body ...)
      (end-performance-region))))

;; no-overhead (i.e. no measuring) version:
;; - - - - - - - - - - - -
;(define-syntax-rule (performance-region [tag0-expr tag-expr ...] body ...)
;  (let () body ...))