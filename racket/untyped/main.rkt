#lang racket/base

(module reader syntax/module-reader untyped)

(require racket/match
         racket/promise
         racket/set
         syntax/parse/define
         (for-syntax racket/base))

(provide #%module-begin
         #%top-interaction
         #%top
         (rename-out [un-λ λ]
                     [un-app #%app]
                     [un-let let]
                     [un-datum #%datum]))

(define (make-fresh id in-scope)
  (if (set-member? in-scope id)
      (make-fresh (string->symbol (format "~a′" id)) in-scope)
      id))

(define (reify expr [scope (set)])
  (cond [(LAM? expr)
         (define id (make-fresh (LAM-id expr) scope))
         (match (reify ((LAM-call expr) id) (set-add scope id))
           [`(λ (,ids ...) ,body) `(λ ,(cons id ids) ,body)]
           [exp `(λ (,id) ,exp)])]
        [(APP? expr)
         (define expr₁ (reify (APP-expr₁ expr) scope))
         (define expr₂ (reify (APP-expr₂ expr) scope))
         (if (and (list? expr₁) (not (equal? (car expr₁) 'λ)))
             (append expr₁ (list expr₂))
             (list expr₁ expr₂))]
        [else expr]))

(define (write-reified expr port mode)
  (define recur (case mode
                  [(#t) write]
                  [(#f) display]
                  [else (λ (p port) (print p port mode))]))
  (recur (reify expr) port))

(struct APP (expr₁ expr₂)
  #:methods gen:custom-write
  [(define write-proc write-reified)])

(struct LAM (id call)
  #:methods gen:custom-write
  [(define write-proc write-reified)])

(define-syntax-parser un-λ
  [(_ (id:id) expr)
   #'(LAM 'id (λ (id) (#%expression (force expr))))]
  [(_ (id:id ids:id ...) expr:expr)
   #'(un-λ (id) (un-λ (ids ...) expr))])

(define-syntax-parser un-app
  [(_ expr:expr) #'expr]
  [(_ expr₁:expr expr₂:expr exprs:expr ...)
   #'(un-app (let ([expr₁′ (force expr₁)]
                   [expr₂′ (lazy expr₂)])
               (if (LAM? expr₁′)
                   ((LAM-call expr₁′) expr₂′)
                   (APP expr₁′ (force expr₂′))))
             exprs ...)])

(define-syntax-parser un-let
  [(_ id:id expr:expr)
   #:with expr′ (local-expand #'expr 'expression null)
   #'(define id expr′)])

(define-syntax-parser un-datum
  [(_ . nat:nat)
   #`(un-λ (s z)
           #,(let loop ([n (syntax->datum #'nat)])
               (if (zero? n)
                   #'z
                   #`(un-app s #,(loop (sub1 n))))))])
