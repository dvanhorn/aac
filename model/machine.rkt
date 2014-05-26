#lang racket
(require redex)
(provide (all-defined-out))

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

;; Set of free variables of an expression
(define-metafunction L
  fv : e -> any
  [(fv x) ,(set (term x))]
  [(fv (App e_1 e_2))
   (∪ (fv e_1) (fv e_2))]
  [(fv (Lam x e))
   ,(set-remove (term (fv e)) (term x))])


;;============================================================================
;; Finite maps

;; Restrict a finite map to a given domain
(define-metafunction L
  ↓ : fin any -> fin
  [(↓ () any) ()]
  [(↓ ((any_d ↦ any_r) any_0 ...) any)
   ((any_d ↦ any_r) any_1 ...)
   (where (any_1 ...) (↓ (any_0 ...) any))
   (side-condition (set-member? (term any) (term any_d)))]
  [(↓ (any_first any_rest ...) any)
   (↓ (any_rest ...) any)])

;; Range of a finite map
(define-metafunction L
  rng : fin -> any
  [(rng ([any_0 ↦ any_1] ...))
   ,(list->set (term (any_1 ...)))])

;; Lookup finite map
(define-metafunction L
  lookup : fin any -> any
  [(lookup (_ ... [any_k ↦ any_v] _ ...) any_k) any_v])

;; Extend finite map
(define-metafunction L
  ext : fin any any -> fin
  [(ext (any ...) any_k any_v) (any ... [any_k ↦ any_v])])

;;============================================================================
;; Sets

(define-term ∅ ,(set))

;; Union of sets
(define-metafunction L
  ∪ : any ... -> any
  [(∪ any ...)
   ,(apply set-union (term (∅ any ...)))])


;;============================================================================
;; The CESK(^) machine
;; - with alloc: this is just the CESK machine
;; - with alloc^: this is a PDA whose naive interpretation may diverge

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

;; Garbage collect state
;; Implements the ceskgc instruction from SeWPR, p172
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

;; Set of live locations
;; Implements the "gc" reduction system from SeWPR, p172
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

;; Live locations from an address
(define-metafunction L
  ll-a : σ a -> any
  [(ll-a σ a)
   (∪ (rng ρ) ...)
   (where ((Clos x e ρ) ...) (lookup σ a))])

;; Live locations from a continuation
(define-metafunction L
  ll-κ : κ -> any
  [(ll-κ ()) ∅]
  [(ll-κ ((AppL e ρ) φ ...))
   (∪ (rng ρ) (ll-κ (φ ...)))]
  [(ll-κ ((AppR (Clos x e ρ)) φ ...))
   (∪ (rng ρ) (ll-κ (φ ...)))])

;; Inject expression into initial machine state
(define-metafunction L
  inj : e -> ς
  [(inj e) (ev e () () ())])

;; Evaluate expression
(define (ev e)
  (apply-reduction-relation* -->_m (term (inj ,e))))
 
;; Visualize concete machine
(define (viz e)
  (traces -->_m (term (inj ,e))))

(define-metafunction L
  alloc : ς -> a
  [(alloc (co κ v ([a ↦ _] ...)))
   ,(+ 1 (apply max -1
                (filter integer?
                        (term (a ...)))))])


;;============================================================================
;; The CESKι(^) machine; CESK with metacontinuations
;; - with alloc: this is just the CESK machine with continuations delimited
;;   at function applications
;; - with alloc^: this is a PDA whose naive interpretation may diverge

;; Added component ι = stack of continuations
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
   ;; When local and meta contination are empty, evaluation is done
   [--> (co () () v σ) (ans v σ) Halt]
   ;; When local continuation is empty, install top continuation
   ;; in metacontinuation
   [--> (co () (κ_0 κ_1 ...) v σ) (co κ_0 (κ_1 ...) v σ) Return]
   
   [--> (co ((AppL e ρ) φ ...) ι v σ)
        (ev e ρ σ ((AppR v) φ ...) ι)
        AppR]
   
   ;; Install an empty local continuation, push current local contination
   ;; to metacontinuation
   [--> (name ς (co ((AppR (Clos x e ρ)) φ ...) (κ ...) v σ))
        (gcι (ev e (↓ (ext ρ x a) (fv e)) (⊔ σ a v) () ((φ ...) κ ...)))
        β
        (where a (allocι ς))]))

;; Just like gc, but fetch live addresses from metacontinuation
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


;;============================================================================
;; The CESKτ(^) machine; CESK with table of metacontinuations
;; - with alloc: this is just the CESK machine with continuations delimited
;;   at function applications and stored in global table
;; - with alloc^: this is a PDA whose naive interpretation is finite

;; Replace ι with τ, which is a pointer into a table metacontinuation segments
(define-extended-language Lτ Lι
  ;; Machine states
  [ς (ev e ρ σ κ τ)
     (co κ τ v σ)
     (ans v σ)]
  [τ (v v σ)  ;; calling context
     ()]      ;; top-level context
    
  [ςK ς K]
  
  ;; τ -> [Set (κ τ)]
  [K (side-condition any_K (hash? (term any_K)))]
  
  ;; [Set τ]
  [τs (side-condition any_τs 
                      (and (set? (term any_τs))
                           (for/and ([x (in-set (term any_τs))])
                             (redex-match? Lτ τ x))))]
  ;; [Set κ]
  [κs (side-condition any_κs 
                      (and (set? (term any_κs))
                           (for/and ([x (in-set (term any_κs))])
                             (redex-match? Lτ κ x))))])

;; Just like gcι but use reachable continuations for root set
(define-metafunction Lτ
  gcτ : ς K -> ς
  [(gcτ (ev e ρ σ κ τ) K)
   (ev e ρ_0 σ_0 κ τ)
   (where ρ_0 (↓ ρ (fv e)))
   (where (κ_0 ...) (reachable-κ K τ))
   (where σ_0 (↓ σ (live ∅ (∪ (rng ρ) (ll-κ κ) (ll-κ κ_0) ...) σ)))]
  [(gcτ (co κ τ (Clos x e ρ) σ) K)
   (co κ τ (Clos x e ρ_0) σ_0)
   (where ρ_0 (↓ ρ (fv e)))
   (where (κ_0 ...) (reachable-κ K τ))
   (where σ_0 (↓ σ (live ∅ (∪ (rng ρ) (ll-κ κ) (ll-κ κ_0) ...) σ)))])

;; Worklist algorithm for set of reachable continuations
(define-metafunction Lτ
  reach-τ : K τs τs κs -> κs
  [(reach-τ K τs_frontier τs_seen κs)
   κs
   (side-condition (set-empty? (term τs_frontier)))]

  [(reach-τ K τs_frontier τs_seen κs)
   (reach-τ K ,(set-rest (term τs_frontier)) τs_seen κs)
   (where () ,(set-first (term τs_frontier)))]

  [(reach-τ K τs_frontier τs_seen κs)
   (reach-τ K τs_frontier* τs_seen* κs_*)
   (where τ ,(set-first (term τs_frontier)))
   (where ((κ_1 τ_1) ...) ,(set->list (hash-ref (term K) (term τ))))
   (where κs_* (∪ κs ,(list->set (term (κ_1 ...)))))
   (where τs_seen* (∪ τs_seen ,(set (term τ))))
   (where τs_frontier*
          ,(set-subtract (term (∪ τs_frontier ,(list->set (term (τ_1 ...)))))
                         (term (∪ τs_seen ,(set (term τ))))))])

;; Reachable continuations
(define-metafunction Lτ
  reachable-κ : K τ -> (κ ...)
  [(reachable-κ K τ)
   ,(set->list (term (reach-τ K ,(set (term τ)) ∅ ∅)))])

;; [Set ς] K -> [Set ς] K
;; The step function for the system
(define (step ςs K) 
  (values (set-apply-reduction-relation (-->_mτ K) ςs)
          (combine-K K (set-apply-reduction-relation update-K ςs))))

;; Reduction split between two relations:
;; -->_mτ computes next state given current table
;; update-K computes update to table given current state

;; Compute diff for table from state (only apply states are relevant)
(define update-K
  (reduction-relation
   Lτ
   #:domain ςK
   [--> (co ((AppR v_f) φ ...) τ_0 v σ)
        ,(hash (term τ) (set (term ((φ ...) τ_0))))
        (where τ (v_f v σ))]))

;; Just like -->_mι but use table to fetch outer continuation
;; from metacontination.
(define (-->_mτ K)
  (reduction-relation
   Lτ
   #:domain ς
   ;; Eval transitions
   [--> (ev x ρ σ κ τ) (gcτ (co κ τ v σ) ,K)
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
        (gcτ (ev e (↓ (ext ρ x a) (fv e)) (⊔ σ a v) () τ) K_1)
        β
        (where τ ((Clos x e ρ) v σ))
        (where a (allocτ ς))
        
        (where K_1 ,(hash-join K (term τ) (term ((φ ...) τ_0))))]))

(define (hash-join h k v)
  (hash-set h k (set-add (hash-ref h k (set)) v)))

(define-metafunction Lτ
  ⊔ : σ a s -> σ
  [(⊔ (name σ (any_1 ... [a ↦ (_ ... s_i _ ...)] any_2 ...)) a s_i)
   σ]
  [(⊔ (any_1 ... [a ↦ (s ...)] any_2 ...) a s_i)
   (any_1 ... [a ↦ (s ... s_i)] any_2 ...)]
  [(⊔ (any ...) a s) (any ... [a ↦ {s}])])

;; Relation [Set Term] -> [Set Term]
;; Lift a reduction relation to a set of terms.
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
  
;; Monovariant abstraction
(define-metafunction Lτ
  allocτ : ς -> a  
  [(allocτ (co ((AppR (Clos x e ρ)) φ ...) τ_0 v σ))
   x])

;; Graph = [Hash ς [Set ς]]

;; Graph Relation [Set ς] -> Graph
(define (update-graph G r ςs)
  (for/fold ([G G])
    ([ς (in-set ςs)])    
    (hash-set G ς (set-union (list->set (apply-reduction-relation r ς))
                             (hash-ref G ς (set))))))

;; Analyze expression producing graph and table
(define (analyze e)  
  (let loop ([seen (set)]
             [ςs (set (term (injι ,e)))]
             [K (hash)]
             [G (hash)])
    
    (cond [(set-empty? ςs) (values K G)]
          [else
           (define-values (ςs1 K1) (step ςs K))
           (loop (set-union seen ςs)
                 (set-subtract ςs1 seen)
                 K1                 
                 (update-graph G (-->_mτ K) ςs))])))
                 
;; Visualize a graph as a reduction relation starting from root.
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

(test-->>∃ -->_m (term (inj EG))
           (redex-match L (ans (Clos one one ()) ())))

(test-->>∃ -->_mι (term (injι EG))
           (redex-match Lι (ans (Clos one one ()) σ)))


;; Note: you get exact computation with GC on this one!
#;
(visualize-graph myG (term (injι EG)))
