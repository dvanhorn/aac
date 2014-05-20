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


(define-metafunction L
  fv : e -> any
  [(fv x) ,(set (term x))]
  [(fv (App e_1 e_2))
   ,(set-union (term (fv e_1))
               (term (fv e_2)))]
  [(fv (Lam x e))
   ,(set-remove (term (fv e)) (term x))])

(define-metafunction L
  ↓ : fin any -> fin
  [(↓ () any) ()]
  [(↓ ((any_d ↦ any_r) any_0 ...) any)
   ((any_d ↦ any_r) any_1 ...)
   (where (any_1 ...) (↓ (any_0 ...) any))
   (side-condition (set-member? (term any) (term any_d)))]
  [(↓ (any_first any_rest ...) any)
   (↓ (any_rest ...) any)])


(define-term ∅ ,(set))

(define-metafunction L
  ∪ : any ... -> any
  [(∪ any ...)
   ,(apply set-union (term (∅ any ...)))])

(define-metafunction L
  gc : ς -> ς
  [(gc (ev e ρ σ κ))
   (ev e ρ_0 σ_0 κ)
   (where ρ_0 (↓ ρ (fv e)))
   (where σ_0 (↓ σ (live ∅ (∪ (rng ρ) (ll-κ κ)) σ)))]
  [(gc (co κ (Clos x e ρ) σ))
   (co κ (Clos x e ρ_0) σ_0)
   (where ρ_0 (↓ ρ (fv e)))
   (where σ_0 (↓ σ (live ∅ (∪ (rng ρ) (ll-κ κ)) σ)))])


(define-metafunction L
  live : any any σ -> any
  [(live any_g any_b σ) 
   any_b
   (side-condition (set-empty? (term any_g)))]
  [(live any_g any_b σ)
   (live any_g0 any_b0 σ)
   (where a ,(set-first (term any_g)))
   (where any_g0 ,(set-subtract
                   (term (∪ any_g (ll-a σ a)))
                   (term (∪ any_b ,(set (term a))))))
   (where any_b0 (∪ any_b ,(set (term a))))])


(define-metafunction L
  ll-a : σ a -> any
  [(ll-a σ a)
   (∪ (rng ρ) ...)
   (where ((Clos x e ρ) ...) (lookup σ a))])


(define-metafunction L
  rng : fin -> any
  [(rng ([any_0 ↦ any_1] ...))
   ,(list->set (term (any_1 ...)))])

(define-metafunction L
  ll-κ : κ -> any
  [(ll-κ ()) ∅]
  [(ll-κ ((AppL e ρ) φ ...))
   ,(set-union (term (rng ρ))
               (term (ll-κ (φ ...))))]
  [(ll-κ ((AppR (Clos x e ρ)) φ ...))
   ,(set-union (term (rng ρ))
               (term (ll-κ (φ ...))))])             

;; Abstract machine in eval/apply form
(define -->_m
  (reduction-relation
   L
   #:domain ς
   ;; Eval transitions
   [--> (ev x ρ σ κ) (gc (co κ v σ))
        Var
        (where (_ ... v _ ...) (lookup σ (lookup ρ x)))] 
   [--> (ev (App e_0 e_1) ρ σ (φ ...))
        (ev e_0 (↓ ρ (fv e_0)) σ ((AppL e_1 (↓ ρ (fv e_1))) φ ...))
        AppL]
   [--> (ev (Lam x e) ρ σ κ)
        (co κ (Clos x e (↓ ρ (fv e))) σ)
        Lam]
   ;; Continue transitions
   [--> (co () v σ) (ans v σ) Halt]
   [--> (co ((AppL e ρ) φ ...) v σ)
        (ev e ρ σ ((AppR v) φ ...))
        AppR]
   [--> (name ς (co ((AppR (Clos x e ρ)) φ ...) v σ))
        (gc (ev e (↓ (ext ρ x a) (fv e)) (⊔ σ a v) (φ ...)))
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
  [ς (ev e ρ σ κ ι)
     (co κ ι v σ)
     (ans v σ)]  
  ;; Meta continuations
  [ι (κ ...)])
 

;; Abstract machine in eval/apply form
;; with heap-allocated stack frames
(define -->_mι
  (reduction-relation
   Lι
   #:domain ς
   ;; Eval transitions
   [--> (ev x ρ σ κ ι) (gcι (co κ ι v σ))
        Var
        (where (_ ... v _ ...) (lookup σ (lookup ρ x)))]
   [--> (ev (App e_0 e_1) ρ σ (φ ...) ι)
        (ev e_0 (↓ ρ (fv e_0)) σ ((AppL e_1 (↓ ρ (fv e_1))) φ ...) ι)
        AppL]
   [--> (ev (Lam x e) ρ σ κ ι)
        (co κ ι (Clos x e (↓ ρ (fv e))) σ)
        Lam]
   ;; Continue transitions
   [--> (co () () v σ) (ans v σ) Halt]
   [--> (co () (κ_0 κ_1 ...) v σ) (co κ_0 (κ_1 ...) v σ) Return] ;;*****
   
   [--> (co ((AppL e ρ) φ ...) ι v σ)
        (ev e ρ σ ((AppR v) φ ...) ι)
        AppR]
   [--> (name ς (co ((AppR (Clos x e ρ)) φ ...) (κ ...) v σ))
        (gcι (ev e (↓ (ext ρ x a) (fv e)) (⊔ σ a v) () ((φ ...) κ ...)))
        β
        (where a (allocι ς))]))

(define-metafunction Lι
  gcι : ς -> ς
  [(gcι (ev e ρ σ κ (κ_1 ...)))
   (ev e ρ_0 σ_0 κ (κ_1 ...))
   (where ρ_0 (↓ ρ (fv e)))
   (where σ_0 (↓ σ (live ∅ (∪ (rng ρ) (ll-κ κ) (ll-κ κ_1) ...) σ)))]
  [(gcι (co κ (κ_1 ...) (Clos x e ρ) σ))
   (co κ (κ_1 ...) (Clos x e ρ_0) σ_0)
   (where ρ_0 (↓ ρ (fv e)))
   (where σ_0 (↓ σ (live ∅ (∪ (rng ρ) (ll-κ κ) (ll-κ κ_1) ...) σ)))])

(define-metafunction Lι
  allocι : ς -> a
  [(allocι (co κ ι v ([a ↦ _] ...)))
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


(define-extended-language Lτ Lι
  ;; Machine states
  [ς (ev e ρ σ κ τ)
     (co κ τ v σ)
     (ans v σ)]   
  [τ (v v σ) ()]
    
  [ςK ς K]
  
  ;; τ -> [Set (κ τ)]
  [K (side-condition any_K (hash? (term any_K)))])
  

(define-metafunction Lτ
  gcτ : ς K -> ς
  [(gcτ (ev e ρ σ κ τ) K)
   (ev e ρ_0 σ_0 κ τ)
   (where ρ_0 (↓ ρ (fv e)))
   (where (κ_0 ...) (r K τ))
   (where σ_0 (↓ σ (live ∅ (∪ (rng ρ) (ll-κ κ) (ll-κ κ_0) ...) σ)))]
  [(gcτ (co κ τ (Clos x e ρ) σ) K)
   (co κ τ (Clos x e ρ_0) σ_0)
   (where ρ_0 (↓ ρ (fv e)))
   (where (κ_0 ...) (r K τ))
   (where σ_0 (↓ σ (live ∅ (∪ (rng ρ) (ll-κ κ) (ll-κ κ_0) ...) σ)))])


(define-metafunction Lτ
  reach-τ : K any_τs-frontier any_τs-seen any_κs -> any_κs
  [(reach-τ K any_τs-frontier any_τs-seen any_κs)
   any_κs
   (side-condition (set-empty? (term any_τs-frontier)))]
  
  [(reach-τ K any_τs-frontier any_τs-seen any_κs)
   (reach-τ K ,(set-rest (term any_τs-frontier)) any_τs-seen any_κs)    
   (where () ,(set-first (term any_τs-frontier)))]
  
  [(reach-τ K any_τs-frontier any_τs-seen any_κs)
   (reach-τ K any_τs-frontier* any_τs-seen* any_κs*)
   
   (where τ ,(set-first (term any_τs-frontier)))
   
   (where ((κ_1 τ_1) ...) ,(set->list (hash-ref (term K) (term τ))))
   (where any_κs* (∪ any_κs ,(list->set (term (κ_1 ...)))))
   (where any_τs-seen* (∪ any_τs-seen ,(set (term τ))))
   (where any_τs-frontier* ,(set-subtract (term (∪ any_τs-frontier ,(list->set (term (τ_1 ...)))))
                                          (term (∪ any_τs-seen ,(set (term τ))))))])

(define-metafunction Lτ
  r : K τ -> (κ ...)
  [(r K τ)
   ,(set->list (term (reach-τ K ,(set (term τ)) ∅ ∅)))])

(define update-K
  (reduction-relation
   Lτ
   #:domain ςK
   [--> (co ((AppR v_f) φ ...) τ_0 v σ)
        ,(hash (term τ) (set (term ((φ ...) τ_0))))
        (where τ (v_f v σ))]))
   
(define (-->_mτ K)
  (reduction-relation
   Lτ
   #:domain ς
   ;; Eval transitions
   [--> (ev x ρ σ κ τ) (co κ τ v σ)
        Var
        (where (_ ... v _ ...) (lookup σ (lookup ρ x)))]   
   [--> (ev (App e_0 e_1) ρ σ (φ ...) τ)
        (ev e_0 (↓ ρ (fv e_0)) σ ((AppL e_1 (↓ ρ (fv e_1))) φ ...) τ)
        AppL]
   [--> (ev (Lam x e) ρ σ κ τ)
        (co κ τ (Clos x e (↓ ρ (fv e))) σ)
        Lam]
   ;; Continue transitions
   [--> (co () () v σ) (ans v σ) Halt]
   [--> (co () τ_0 v σ)
        (co κ τ v σ)
        (side-condition (not (empty? (term τ_0))))
        (where (_ ... (κ τ) _ ...)
               ,(set->list (hash-ref K (term τ_0))))]             
   [--> (co ((AppL e ρ) φ ...) τ v σ)
        (ev e ρ σ ((AppR v) φ ...) τ)
        AppR]
   [--> (name ς (co ((AppR (Clos x e ρ)) φ ...) τ_0 v σ))
        (ev e (↓ (ext ρ x a) (fv e)) (⊔ σ a v) () τ)
        β
        (where τ ((Clos x e ρ) v σ))
        (where a (allocτ ς))]))

(define-metafunction Lτ
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
     [(τ κs) (in-hash K)])
    (hash-set K0 τ 
              (set-union κs (hash-ref K0 τ (set))))))
  

(define-metafunction Lτ
  allocτ : ς -> a  
  [(allocτ (co ((AppR (Clos x e ρ)) φ ...) τ_0 v σ))
   x])

;; [Set ς] K -> [Set ς] K
(define (step ςs K) 
  (values (set-apply-reduction-relation (-->_mτ K) ςs)
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
                 (update-graph G (-->_mτ K) ςs))])))
                 

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

;(viz (term EG)) 
;(vizι (term EG))
(test-->> -->_m (term (inj (App (Lam x ZERO) ONE)))
          (term (ans (Clos zero zero ()) ())))
(test-->> -->_mι (term (injι (App (Lam x ZERO) ONE)))
          (term (ans (Clos zero zero ()) ())))



(visualize-graph myG (term (injι EG)))

(test-->>∃ -->_m (term (inj EG))
           (redex-match L (ans (Clos one one ()) ())))

(test-->>∃ -->_mι (term (injι EG))
           (redex-match Lι (ans (Clos one one ()) σ)))
