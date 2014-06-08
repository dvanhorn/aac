#lang racket

(define-syntax-rule (for*/union guards body ...)
  (for*/fold ([acc (set)]) guards (set-union acc (let () body ...))))

(define (hash-add h k v)
  (hash-set h k (set-add (hash-ref h k (set)) v)))

(define T (make-hash))
(struct state (point σ) #:transparent)

(struct ref (x) #:transparent)
(struct app (e0 e1) #:transparent)
(struct lam (x e) #:transparent)

(define (alloc x) x)
(define (sim s)
  (match (hash-ref T s #f)
    [#f (hash-set! T s #t)
        (define res
          (match s
            [(state (cons (ref x) ρ) σ)
             (define a (hash-ref ρ x (λ () (error 'var-lookup "Var ~a" x))))
             (for/set ([v (in-set (hash-ref σ a (λ () (error 'addr-lookup "Addr ~a" a))))])
               (state v σ))]
            [(state (cons (lam x e) ρ) σ) (set s)] ;; values self-evaluate
            [(state (cons (app e0 e1) ρ) σ)
             (for*/union ([fn (in-set (sim (state (cons e0 ρ) σ)))]
                          [fnv (in-value (state-point fn))]
                          [ar (in-set (sim (state (cons e1 ρ) (state-σ fn))))])
               (match-define (cons (lam x e) ρ) fnv)
               (define a (alloc x))
               (define ρ* (hash-set ρ x a))
               (define σ* (hash-add (state-σ ar) a (state-point ar)))
               (sim (state (cons e ρ*) σ*)))]
            [_ (set)]))
        (hash-set! T s res)
        res]
    [#t (set)] ;; infinite loop
    [results results]))

(define (analyze e)
  (hash-clear! T)
  (define final (sim (state (cons e (hash)) (hash))))
  (values final T))

;; (id id)
(analyze (app (lam 'x (ref 'x))
              (lam 'y (ref 'y))))

;; Ω
(analyze (app (lam 'x (app (ref 'x) (ref 'x)))
              (lam 'y (app (ref 'y) (ref 'y)))))
