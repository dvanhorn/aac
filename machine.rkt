#lang racket
(require redex)
 
(define-language L
  ;; Expressions
  [e x (App e e) (Lam x e)]
  [x variable-not-otherwise-mentioned]
  [v (Clos x e ρ)]
  ;; Finite functions
  [fin ([any ↦ any] ...)]
  ;; Machine states
  [ς (ev e ρ σ κ)
     (co κ v σ)
     (ans v σ)]
  ;; Environments
  [ρ ([x ↦ a] ...)]
  ;; Stores
  [σ ([a ↦ (s ...)] ...)]
  ;; Storables
  [s v]    
  ;; Continuations
  [κ (φ ...)]  
  ;; Frames
  [φ (AppL e ρ) (AppR v)]
  ;; Addresses
  [(a b c) any])
             

;; Abstract machine in eval/apply form
(define -->_m
  (reduction-relation
   L
   #:domain ς
   ;; Eval transitions
   [--> (ev x ρ σ κ) (co κ v σ)
        Var
        (where v (lookup σ (lookup ρ x)))]
   [--> (ev (App e_0 e_1) ρ σ (φ ...))
        (ev e_0 ρ σ ((AppL e_1 ρ) φ ...))
        AppL]
   [--> (ev (Lam x e) ρ σ κ)
        (co κ (Clos x e ρ) σ)
        Lam]
   ;; Continue transitions
   [--> (co () v σ) (ans v σ) Halt]
   [--> (co ((AppL e ρ) φ ...) v σ)
        (ev e ρ σ ((AppR v) φ ...))
        AppR]
   [--> (name ς (co ((AppR (Clos x e ρ)) φ ...) v σ))
        (ev e (ext ρ x a) (ext σ a v) (φ ...))
        β
        (where a (alloc ς))]))
 
(define-metafunction L
  inj : e -> ς
  [(inj e) (ev e () () ())])
 
(define (ev e)
  (apply-reduction-relation* -->_m (term (inj ,e))))
 
;; Visualize concete machine
(define (viz e)
  (traces -->_m (term (inj ,e))))
 
(define-metafunction L
  lookup : fin any -> any
  [(lookup (_ ... [any_k ↦ any_v] _ ...) any_k) any_v])
 
(define-metafunction L
  ext : fin any any -> fin
  [(ext (any ...) any_k any_v) (any ... [any_k ↦ any_v])])
 
(define-metafunction L
  alloc : ς -> a
  [(alloc (co κ v ([a ↦ _] ...)))
   ,(+ 1 (apply max -1
                (filter integer?
                        (term (a ...)))))])
 
#;
(viz '(App (Lam x (App x x)) 
           (Lam y (App y y))))


(define-extended-language Lι L
  ;; Machine states
  [ς (ev e ρ σ ι κ)
     (co ι κ v σ)
     (ans v σ)]
  ;; Meta continuations
  [κ (ι ...)]
  ;; Local continuations
  [ι (φ ...)])
 

;; Abstract machine in eval/apply form
;; with heap-allocated stack frames
(define -->_mι
  (reduction-relation
   Lι
   #:domain ς
   ;; Eval transitions
   [--> (ev x ρ σ ι κ) (co ι κ v σ)
        Var
        (where v (lookup σ (lookup ρ x)))]
   [--> (ev (App e_0 e_1) ρ σ (φ ...) κ)
        (ev e_0 ρ σ ((AppL e_1 ρ) φ ...) κ)
        AppL]
   [--> (ev (Lam x e) ρ σ ι κ)
        (co ι κ (Clos x e ρ) σ)
        Lam]
   ;; Continue transitions
   [--> (co () () v σ) (ans v σ) Halt]
   [--> (co () (ι_0 ι_1 ...) v σ) (co ι_0 (ι_1 ...) v σ) Return] ;;*****
   
   [--> (co ((AppL e ρ) φ ...) κ v σ)
        (ev e ρ σ ((AppR v) φ ...) κ)
        AppR]
   [--> (name ς (co ((AppR (Clos x e ρ)) φ ...) (ι ...) v σ))
        (ev e (ext ρ x a) (ext σ a v) () ((φ ...) ι ...))
        β
        (where a (allocι ς))]))


(define-metafunction Lι
  allocι : ς -> a
  [(allocι (co ι κ v ([a ↦ _] ...)))
   ,(+ 1 (apply max -1
                (filter integer?
                        (term (a ...)))))])

(define-metafunction Lι
  injι : e -> ς
  [(injι e) (ev e () () () ())])
 
(define (evι e)
  (apply-reduction-relation* -->_mι (term (injι ,e))))
 
;; Visualize concete machine
(define (vizι e)
  (traces -->_mι (term (injι ,e))))

#;
(vizι '(App (Lam x (App x x)) 
            (Lam y (App y y))))
#;
(vizι '(App (Lam f (App (App f f) f)) 
            (Lam y y)))


(define-extended-language LιK Lι
  ;; Machine states
  [ς (ev e ρ σ ι τ)
     (co ι τ v σ)
     (ans v σ)]   
  [τ (v v σ) ()]
    
  [ςK ς K]
  
  ;; τ -> [Set (ι τ)]
  [K (side-condition any_K (hash? (term any_K)))])
  
(define update-K
  (reduction-relation
   LιK
   #:domain ςK
   [--> (co ((AppR v_f) φ ...) τ_0 v σ)
        ,(hash (term τ) (set (term ((φ ...) τ_0))))
        (where τ (v_f v σ))]))
   
(define (-->_mιK K)
  (reduction-relation
   LιK
   #:domain ς
   ;; Eval transitions
   [--> (ev x ρ σ ι τ) (co ι τ v σ)
        Var
        (where (_ ... v _ ...) (lookup σ (lookup ρ x)))]   
   [--> (ev (App e_0 e_1) ρ σ (φ ...) τ)
        (ev e_0 ρ σ ((AppL e_1 ρ) φ ...) τ)
        AppL]
   [--> (ev (Lam x e) ρ σ ι τ)
        (co ι τ (Clos x e ρ) σ)
        Lam]
   ;; Continue transitions
   [--> (co () () v σ) (ans v σ) Halt]
   [--> (co () τ_0 v σ)
        (co ι τ v σ)
        (side-condition (not (empty? (term τ_0))))
        (where (_ ... (ι τ) _ ...)
               ,(set->list (hash-ref K (term τ_0))))]             
   [--> (co ((AppL e ρ) φ ...) τ v σ)
        (ev e ρ σ ((AppR v) φ ...) τ)
        AppR]
   [--> (name ς (co ((AppR (Clos x e ρ)) φ ...) τ_0 v σ))
        (ev e (ext ρ x a) (⊔ σ a v) () τ)
        β
        (where τ ((Clos x e ρ) v σ))
        (where a (allocιK ς))]))

(define-metafunction LιK
  ⊔ : σ a s -> σ
  [(⊔ (name σ (any_1 ... [a ↦ (_ ... s_i _ ...)] any_2 ...)) a s_i)
   σ]
  [(⊔ (any_1 ... [a ↦ (s ...)] any_2 ...) a s_i)
   (any_1 ... [a ↦ (s ... s_i)] any_2 ...)]
  [(⊔ (any ...) a s) (any ... [a ↦ {s}])])



;; Relation [Set Term] -> [Set Term]
(define (set-apply-reduction-relation r s)
  (for/fold ([y (set)])
    ((x (in-set s)))
    (set-union y (list->set (apply-reduction-relation r x)))))

;; K [Set K] -> K
(define (combine-K K0 Ks)
  (for*/fold ([K0 K0])
    ([K (in-set Ks)]
     [(τ ιs) (in-hash K)])
    (hash-set K0 τ 
              (set-union ιs (hash-ref K0 τ (set))))))
  

(define-metafunction LιK
  allocιK : ς -> a
  
  [(allocιK (co ((AppR (Clos x e ρ)) φ ...) τ_0 v σ))
   x]
  
  #;
  [(allocιK (co ι τ v ([a ↦ _] ...)))
   ,(+ 1 (apply max -1
                (filter integer?
                        (term (a ...)))))])

;; [Set ς] K -> [Set ς] K
(define (step ςs K) 
  (values (set-apply-reduction-relation (-->_mιK K) ςs)
          (combine-K K (set-apply-reduction-relation update-K ςs))))



;; Graph = [Hash ς [Set ς]]


(define (update-graph G -> ςs)
  (for/fold ([G G])
    ([ς (in-set ςs)])    
    (hash-set G ς (set-union (list->set (apply-reduction-relation -> ς))
                             (hash-ref G ς (set))))))

(define (analyze e)  
  (let loop ([seen (set)]
             [ςs (set (term (injι ,e)))]
             [K (hash)]
             [G (hash)])
    
    (cond [(set-empty? ςs) (values K G)]
          [else
           (define-values (ςs1 K1) (step ςs K))
           ;(printf "ςs: ~a~nK: ~a~n~n" ςs1 K1)
           (loop (set-union seen ςs)
                 (set-subtract ςs1 seen)
                 K1                 
                 (update-graph G (-->_mιK K) ςs))])))
                 

#;
(define-values (myK myG)
  (analyze (term (App (Lam y (App y y)) 
                      (Lam x (App x x))))))

(define (visualize-graph G root)
  (define-language FOO)
  (traces
   (reduction-relation 
    FOO
    (--> any_0 any_1
         (where (_ ... any_1 _ ...)
                ,(set->list (hash-ref G (term any_0) '())))))
   root))
  
#;
(let* ([id (λ (q) ((λ (x) x) q))]
       [y (id ZERO)]
       [z (id ONE)])  
  z)
(define-term ID (Lam q (App (Lam x x) q)))
(define-term ZERO (Lam zero zero))
(define-term ONE (Lam one one))

(define-term EG
  (App (Lam id 
            (App (Lam y (App (Lam z z) (App id ONE))) (App id ZERO))) ID))
 
;; Sanity check: you either get ZERO or ONE, but
;; there is no loop!
(define-values (myK myG)
  (analyze (term EG)))

(visualize-graph myG (term (injι EG)))


