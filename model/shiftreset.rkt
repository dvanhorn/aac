#lang racket
(require "machine.rkt" (for-syntax syntax/parse))
(require redex)

(define-extended-language SR L
  [e .... (shift x e) (reset e)
     ;; added for testing purposes
     (op2 e e) primv]
  [op2 + *]
  [φ .... (op2L op2 e ρ) (op2R op2 v)]
  [κ (φ ...)]
  [primv number #t #f]
  [C (κ ...)]
  [v .... (comp κ) primv]
  [ς (ev e ρ σ κ C)
     (co κ C v σ)
     (ans v σ)])

(define-syntax (values->list stx)
  (syntax-parse stx
    [(_ n:nat e:expr)
     (with-syntax ([(x ...) (generate-temporaries (build-list (syntax-e #'n) values))])
      #'(let-values ([(x ...) e]) (list x ...)))]))

(define-metafunction SR
  inj-sr : e -> ς
  [(inj-sr e) (ev e () () () ())])

(define-metafunction SR
  alloc-sr : ς -> any
  [(alloc-sr (co κ C v ([a ↦ _] ...)))
   ,(+ 1 (apply max -1 (filter integer? (term (a ...)))))]
  [(alloc-sr (ev (shift x e) ρ ([a ↦ _] ...) κ C))
   ,(+ 1 (apply max -1 (filter integer? (term (a ...)))))])

(define-metafunction SR
  fv-sr : e -> any
  [(fv-sr x) ,(set (term x))]
  [(fv-sr (App e_1 e_2))
   (∪ (fv-sr e_1) (fv-sr e_2))]
  [(fv-sr (Lam x e))
   ,(set-remove (term (fv-sr e)) (term x))]
  [(fv-sr (reset e)) (fv-sr e)]
  [(fv-sr (shift x e)) ,(set-remove (term (fv-sr e)) (term x))]
  [(fv-sr (op2 e_1 e_2))
   (∪ (fv-sr e_1) (fv-sr e_2))]
  [(fv-sr primv) ∅])

;; Metafunction extension sucks.
;; We can't just add a new value and expect ll-κ to work.
(define-metafunction SR
  ll-sr-κ : κ -> any
  [(ll-sr-κ ()) ∅]
  [(ll-sr-κ ((AppL e ρ) φ ...))
   (∪ (rng ρ) (ll-sr-κ (φ ...)))]
  [(ll-sr-κ ((AppR v) φ ...))
   (∪ (touched v) (ll-sr-κ (φ ...)))]
  [(ll-sr-κ ((op2L op2 e ρ) φ ...))
   (∪ (rng ρ) (ll-sr-κ (φ ...)))]
  [(ll-sr-κ ((op2R op2 v) φ ...))
   (ll-sr-κ (φ ...))])

(define-metafunction SR
  ll-C : C -> any
  [(ll-C (κ ...)) (∪ (ll-sr-κ κ) ...)])

(define-metafunction SR
  touched : v -> any
  [(touched (Clos x e ρ)) (rng ρ)]
  [(touched (comp κ)) (ll-sr-κ κ)]
  [(touched primv) ∅])

;; Live locations from an address
(define-metafunction SR
  ll-sr-a : σ a -> any
  [(ll-sr-a σ a)
   (∪ (touched v) ...)
   (where (v ...) (lookup σ a))])

(define-metafunction SR
  live-sr : any any σ -> any
  [(live-sr any_g any_b σ)
   any_b
   (side-condition (set-empty? (term any_g)))]
  [(live-sr any_g any_b σ)
   (live-sr any_g0 any_b0 σ)
   (where a ,(set-first (term any_g)))
   (where any_g0 ,(set-subtract
                   (term (∪ any_g (ll-sr-a σ a)))
                   (term (∪ any_b ,(set (term a))))))
   (where any_b0 (∪ any_b ,(set (term a))))])

(define-metafunction SR
  gc-sr : ς -> ς
  [(gc-sr (ev e ρ σ κ C))
   (ev e ρ_0 σ_0 κ C)
   (where ρ_0 (↓ ρ (fv-sr e)))
   (where σ_0 (↓ σ (live-sr ∅ (∪ (rng ρ) (ll-sr-κ κ) (ll-C C)) σ)))]
  [(gc-sr (co κ C (Clos x e ρ) σ))
   (co κ C (Clos x e ρ_0) σ_0)
   (where ρ_0 (↓ ρ ,(set-remove (term (fv-sr e)) (term x))))
   (where σ_0 (↓ σ (live-sr ∅ (∪ (rng ρ) (ll-sr-κ κ) (ll-C C)) σ)))]
  [(gc-sr (co κ C primv σ))
   (co κ C primv σ_0)
   (where σ_0 (↓ σ (live-sr ∅ (∪ (ll-sr-κ κ) (ll-C C)) σ)))]
  [(gc-sr (co κ C (comp κ_1) σ))
   (co κ C (comp κ_1) σ_0)
   (where σ_0 (↓ σ (live-sr ∅ (∪ (ll-sr-κ κ) (ll-sr-κ κ_1) (ll-C C)) σ)))])

(define-metafunction SR
  δ : op2 primv primv -> primv
  [(δ + number_0 number_1) ,(+ (term number_0) (term number_1))]
  [(δ * number_0 number_1) ,(* (term number_0) (term number_1))])

(define -->_sr
  (reduction-relation
   SR
   #:domain ς
   ;; Eval transitions
   [--> (ev x ρ σ κ C) (gc-sr (co κ C v σ))
        Var
        (where (_ ... v _ ...) (lookup σ (lookup ρ x)))]
   [--> (ev (App e_0 e_1) ρ σ (φ ...) C)
        (ev e_0 (↓ ρ (fv-sr e_0)) σ ((AppL e_1 (↓ ρ (fv-sr e_1))) φ ...) C)
        AppL]
   [--> (ev (Lam x e) ρ σ κ C)
        (co κ C (Clos x e (↓ ρ (fv-sr e))) σ)
        Lam]
   [--> (name ς (ev (shift x e) ρ σ κ C))
        (ev e (ext ρ x a) (⊔ σ a (comp κ)) () C)
        Shift
        (where a (alloc-sr ς))]
   [--> (ev (reset e) ρ σ κ_0 (κ ...))
        (ev e ρ σ () (κ_0 κ ...))
        Reset]
   ;; Eval transitions for primitives
   [--> (ev primv ρ σ κ C)
        (co κ C primv σ)
        Datum]
   [--> (ev (op2 e_0 e_1) ρ σ (φ ...) C)
        (ev e_0 ρ σ ((op2L op2 e_1 ρ) φ ...) C)
        op2L]
   ;; Continue transitions
   [--> (co () (κ_0 κ ...) v σ) (co κ_0 (κ ...) v σ)
        Pop-prompt]
   [--> (co () () v σ) (ans v σ) Halt]
   [--> (co ((AppL e ρ) φ ...) C v σ)
        (ev e ρ σ ((AppR v) φ ...) C)
        AppR]
   [--> (name ς (co ((AppR (Clos x e ρ)) φ ...) C v σ))
        (gc-sr (ev e (↓ (ext ρ x a) (fv-sr e)) (⊔ σ a v) (φ ...) C))
        β-fn
        (where a (alloc-sr ς))]
   [--> (co ((AppR (comp κ_0)) φ ...) (κ ...) v σ)
        (co κ_0 ((φ ...) κ ...) v σ)
        β-comp]
   ;; Continue transitions for primitives
   [--> (co ((op2L op2 e ρ) φ ...) C v σ)
        (ev e ρ σ ((op2R op2 v) φ ...) C)
        op2R]
   [--> (co ((op2R op2 v_0) φ ...) C v_1 σ)
        (co (φ ...) C v σ)
        δ
        (where v (δ op2 v_0 v_1))]))

(define-extended-language SRι SR
  [ς (ev e ρ σ χ ι κ C)
     (co ι κ C v σ χ)
     (ans v σ χ)]
  [τ (v v σ χ) τ̂] ;; calling contexts
  [τ̂ (v v a)] ;; approximated contexts for storing
  [υ (e ρ σ χ) (κ̃ v σ χ)] ;; prompt contexts
  ;; meta Ξ
  [ςs (ς ...)]
  [sys (ςs Ξ Ξ)]
  [Ξ (side-condition any_Ξ (hash? (term any_Ξ)))]
  [ςK ς (Ξ Ξ)]
  [χ ([a ↦ (σ ...)] ...)]
  [ι (φ ...)]
  [κ̃ () (approx ι τ̂)]
  [κ () τ τ̂]
  [C () υ]
  [v (Clos x e ρ) (comp κ̃) primv])

(define-metafunction SRι
  inj-srι : e -> ς
  [(inj-srι e) (ev e () () () () () ())])

(define-metafunction SRι
  ll-κι : κ χ Ξ -> any
  [(ll-κι () χ Ξ) ()]
  [(ll-κι τ χ Ξ) ,(set->list (term (reach-τι Ξ ,(set (term τ)) ∅ ∅)))])

;; TODO
(define-metafunction SRι
  gc-srι : ς Ξ Ξ -> ς
  [(gc-srι ς _ _) ς])

#;
(define-metafunction SRι
  gc-srι : ς Ξ Ξ -> ς
  [(gc-srι (ev e ρ σ χ ι κ C) Ξ_κ Ξ_C)
   (ev e ρ_0 σ_0 χ_0 ι κ C)
   (where ρ_0 (↓ ρ (fv-sr e)))
   (where (ι_0 ...) (reachable-ι κ χ Ξ_κ))
   ;;; FIXME!
   (where (κ_0 ...) (reachable-κι C Ξ_C))
   (where (ι_1 ...) (∪ (reachable-ι κ_0 χ Ξ_κ)))
   (where any_live (live-sr ∅ (∪ (rng ρ) (ll-sr-κ ι) (ll-sr-κ ι_0) ...) σ))
   (where σ_0 (↓ σ any_live))
   (where χ_0 (↓ χ any_live))]
  [(gc-srι (co ι κ C (Clos x e ρ) σ χ) Ξ_κ Ξ_C)
   (co ι κ C (Clos x e ρ_0) σ_0 χ_0)
   (where ρ_0 (↓ ρ ,(set-remove (term (fv-sr e)) (term x))))
   (where any_live (live-sr ∅ (∪ (rng ρ) (ll-sr-κ ι) (ll-κι κ χ Ξ_κ) (ll-Cι C Ξ_C)) σ))
   (where σ_0 (↓ σ any_live))
   (where χ_0 (↓ χ any_live))]
  [(gc-srι (co ι κ C primv σ χ) Ξ_κ Ξ_C)
   (co κ C primv σ_0 χ_0)
   (where any_live (live-sr ∅ (∪ (ll-sr-κ ι) (ll-κι κ χ Ξ_κ) (ll-Cι C Ξ_C)) σ))
   (where σ_0 (↓ σ any_live))
   (where χ_0 (↓ χ any_live))]
  [(gc-srι (co ι κ C (comp κ̃) σ χ) Ξ_κ Ξ_C)
   (co ι κ C (comp κ̃) σ_0 χ_0)
   (where any_live (live-sr ∅ (∪ (ll-sr-κ ι) (ll-κι κ χ Ξ_Κ) (ll-Cι C Ξ_C) (ll-κ̃ κ̃ χ Ξ_κ)) σ))
   (where σ_0 (↓ σ any_live))
   (where χ_0 (↓ χ any_live))])

(define-metafunction SR
  [(alloc-srι (co ι κ C v σ χ) (AppR (Clos x e ρ)))
   x]
  [(alloc-srι (ev (shift x e) ρ σ χ ι κ C))
   (x x)])

(define (-->_srι Ξκ ΞC)
  (reduction-relation
   SRι
   #:domain ς
   ;; Eval transitions
   [--> (ev x ρ σ χ ι κ C)
        (gc-srιι (co ι κ C v σ χ))
        Var
        (where (_ ... v _ ...) (lookup σ (lookup ρ x)))]
   [--> (ev (App e_0 e_1) ρ σ χ (φ ...) κ C)
        (ev e_0 (↓ ρ (fv-sr e_0)) σ χ ((AppL e_1 (↓ ρ (fv-sr e_1))) φ ...) κ C)
        AppL]
   [--> (ev (name le (Lam x e)) ρ σ χ ι κ C)
        (co ι κ C (Clos x e (↓ ρ (fv-sr le))) σ χ)
        Lam]
   [--> (name ς (ev (shift x e) ρ σ χ ι κ C))
        (ev e (ext ρ x a) () (⊔ σ a (comp κ̃)) χ_1 () () C)
        Shift
        (where (a b) (alloc-srι ς))
        (where (κ̃ χ_1) (approximate b χ ι κ))]
   [--> (ev (reset e) ρ σ χ ι κ C)
        (ev e ρ σ χ σ () () τC)
        ;; update τ ↦ ι κ C
        Reset
        (where τC (e ρ σ χ))]
   ;; Eval transitions for primitives
   [--> (ev primv ρ σ χ ι κ C)
        (co ι κ C primv σ χ)
        Datum]
   [--> (ev (op2 e_0 e_1) ρ σ χ (φ ...) κ C)
        (ev e_0 ρ σ χ ((op2L op2 e_1 ρ) φ ...) κ C)
        op2L]
   ;; Continue transitions
   [--> (co () () τC v σ χ)
        (co ι κ C v σ χ)
        Pop-prompt
        (where (_ ... (ι κ C) _ ...) ,(set->list (hash-ref ΞC (term τC) (set))))]
   [--> (co () () () v σ χ) (ans v σ χ) Halt]
   [--> (co ι κ C v σ χ)
        (ev e ρ σ χ ((AppR v) φ ...) κ C)
        AppR
        (where (_ ... (((AppL e ρ) φ ...) κ_1) _ ...) (pop ,Ξκ ι κ))]
   [--> (name ς (co ι κ C v σ χ))
        (gc-srι (ev e (↓ (ext ρ x a) (fv-sr e)) (⊔ σ a v) χ () τ C) ,Ξκ ,ΞC)
        β-fn
        (where (_ ... (((name φ_pop (AppR (Clos x e ρ))) φ ...) κ_1) _ ...) (pop ,Ξκ ι κ))
        (where τ ((Clos x e ρ) v σ χ))
        (where a (alloc-srι ς φ_pop))]
   [--> (co ι κ C v σ χ)
        (gc-srι (co ι_1 κ_1 τC v σ χ))
        β-comp
        (where (_ ... (((AppR (comp κ̃)) φ ...) κ_0) _ ...) (pop ,Ξκ ι κ))
        (where τC (κ̃ v σ χ))
        (where (ι_1 κ_1) ,((term-match/single SRι
                             [() (term (() ()))]
                             [(approx ι τ̂) (term (ι τ̂))])
                           (term κ̃)))]
   ;; Continue transitions for primitives
   [--> (co ι κ C v σ χ)
        (ev e ρ σ χ ((op2R op2 v) φ ...) κ_1 C)
        op2R
        (where (_ ... (((opL op2 e ρ) φ ...) κ_1) _ ...) (pop ,Ξκ ι κ))]
   [--> (co ι κ C v_1 σ χ)
        (close (store (co (φ ...) κ_1 C v) σ) χ)
        δ
        (where (_ ... (((op2R op2 v_0) φ ...) κ_1) _ ...) (pop ,Ξκ ι κ))
        (where v (δ op v_0 v_1))]))

(define-metafunction SRι
  pop : Ξ ι κ -> ((φ ι κ) ...)
  [(pop Ξ_κ ι κ) ,(set->list (term (pop* Ξ_κ ι κ ∅)))])

(define-metafunction SRι
  [(pop* Ξ_κ (φ_0 φ ...) κ _) ,(set (term (φ_0 (φ ...) κ)))]
  [(pop* Ξ_κ () τ any) ,(if (set-member? (term any) (term τ))
                            (term ∅)
                            (for/fold ([acc (set)])
                                ([ικ (in-set (hash-ref (term Ξ_κ) (term τ) (set)))])
                              (match-define (list ι κ) ικ)
                              (set-union acc
                                         (term (pop* Ξ_κ ,ι ,κ ,(set-add (term any) (term τ)))))))])

(define (update-Ξ Ξκ ΞC)
  (reduction-relation
      SRι
    #:domain ςK
    [--> (ev (reset e) ρ σ χ ι κ C)
         (,(hash) ,(hash (term τC) (set (term (ι κ C)))))
         (where τC (e ρ σ χ))]
    [--> (co ι κ C v σ χ)
         ,(values->list 2
                        (begin
                          (printf "Ξκ ~a~%" Ξκ)
                          (for/fold ([Ξκ (hash)] [ΞC (hash)])
                             ([φικ (in-list (term (pop ,Ξκ ι κ)))])
                           (match-define (list φ ι* κ*) φικ)
                           ((term-match/single SRι
                              [(AppR (Clos x e ρ))
                               (values (hash-add Ξκ
                                          (term ((Clos x e ρ) v σ χ))
                                          (term (,ι* ,κ*)))
                                       ΞC)]
                              [(AppR (comp κ̃))
                               (values Ξκ
                                       (hash-add ΞC
                                                 (term (κ̃ v σ χ))
                                                 (term (,ι* ,κ* C))))]
                              [_ (values Ξκ ΞC)])
                            φ))))]))

(define (combine-Ξs Ξκ ΞC Ξs)
  (for/fold ([Ξκ Ξκ] [ΞC ΞC])
      ([2lst (in-set Ξs)])
    (values (for/fold ([Ξκ Ξκ]) ([(τ ικs) (in-hash (first 2lst))])
              (hash-union Ξκ τ ικs))
            (for/fold ([ΞC ΞC]) ([(τC ικCs) (in-hash (second 2lst))])
              (hash-union ΞC τC ικCs)))))

(define (step-srι ςs Ξκ ΞC)
  (define-values (Ξκ1 ΞC1)
    (combine-Ξs Ξκ ΞC (set-apply-reduction-relation (update-Ξ Ξκ ΞC) ςs)))
  (values (set-apply-reduction-relation (-->_srι Ξκ ΞC) ςs)
          Ξκ1 ΞC1))

(define (analyze-srι e)
  (let loop ([seen (set)]
             [ςs (set (term (inj-srι ,e)))]
             [Ξκ (hash)]
             [ΞC (hash)]
             [G (hash)])

    (cond [(set-empty? ςs) (values Ξκ ΞC G)]
          [else
           (define-values (ςs1 Ξκ1 ΞC1) (step-srι ςs Ξκ ΞC))
           (loop (set-union seen ςs)
                 (set-subtract ςs1 seen)
                 Ξκ1 ΞC1
                 (update-graph G (-->_srι Ξκ1 ΞC1) ςs))])))

(define-metafunction SRι
  approximate : any χ ι κ -> (χ κ̃)
  [(approximate a χ ι ()) (χ ())]
  [(approximate a χ ι (v_f v_a σ χ_1))
   ((⊔ (f⊔ χ χ_1) a σ) (approx ι (v_f v_a a)))]
  [(approximate a χ ι (approx ι_1 (v_f v_a b)))
   ((⊔* χ a (lookup χ b)) (approx ι_1 (v_f v_a a)))])

(define-term SHIFT1 (+ 10 (reset (+ 2 (shift k (+ 100 (App k (App k 3))))))))
(define-term SHIFT2 (* 10 (reset (* 2 (shift g (reset (* 5 (shift f (+ (App f 1) 1)))))))))
(define-term SHIFT3 (App (Lam f (+ 1 (reset (+ 10 (App f 100)))))
                         (Lam x (shift k (App k (App k x))))))
(define-syntax-rule (tests --> inj tests ...)
  (begin (traces --> (term (inj tests))) ...))

(define (traces-hat e)
  (let-values ([(myΞκ myΞC myG) (analyze-srι e)])
    (visualize-graph myG (term (inj-srι ,e)))))
(define-syntax-rule (viss tests ...)
  (begin (traces-hat (term tests)) ...))
#;(tests -->_sr inj-sr SHIFT1 SHIFT2 SHIFT3)
(viss SHIFT1 SHIFT2 SHIFT3)
