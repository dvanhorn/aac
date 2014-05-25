#lang racket
(require "machine.rkt")
(require redex)

(define-extended-language CM L
  [e .... (Frame R e) (Grant R e) (Test R e e) Fail]
  [R (r ...)]
  [r variable]
  
  [κ (φ φ ...)]
  ;; Frames
  [φ (AppL e ρ m) (AppR v m) m]
  
  [m [(r ↦ gn) ...]]
  [gn grant no])


;; Assume some finite set of principals
(define P
  (set 'a 'b 'c 'd 'e 'f))

(define-metafunction CM
  complement : R -> R
  [(complement (r ...))
   ,(set->list (set-subtract P (list->set (term (r ...)))))])


;; Abstract machine in eval/apply form
(define -->_cm
  (reduction-relation
   CM
   #:domain ς
   ;; Eval transitions
   [--> (ev x ρ σ κ) (co κ v σ)
        Var
        (where (_ ... v _ ...) (lookup σ (lookup ρ x)))]
   [--> (ev (App e_0 e_1) ρ σ (φ ...))
        (ev e_0 (↓ ρ (fv-cm e_0)) σ ((AppL e_1 (↓ ρ (fv-cm e_1)) ()) φ ...))
        AppL]
   [--> (ev (Lam x e) ρ σ κ)
        (co κ (Clos x e (↓ ρ (fv e))) σ)
        Lam]
   
   ;; Stack inspection transitions
   [--> (ev (Frame R e) ρ σ κ)
        (ev e ρ σ (cont-update κ (complement R) no))
        Frame]   
   [--> (ev (Grant R e) ρ σ κ)
        (ev e ρ σ (cont-update κ R grant))
        Grant]   
   [--> (ev (Test R e_0 e_1) ρ σ κ)
        (ev e_0 ρ σ κ)
        (where #t (OK R κ))
        OK]
   [--> (ev (Test R e_0 e_1) ρ σ κ)
        (ev e_1 ρ σ κ)
        (where #f (OK R κ))
        Not-OK]
   
   ;; Continue transitions
   [--> (co (m) v σ) (ans v σ) Halt]
   [--> (co ((AppL e ρ m) φ ...) v σ)
        (ev e ρ σ ((AppR v ()) φ ...))
        AppR]
   [--> (name ς (co ((AppR (Clos x e ρ) m) φ ...) v σ))
        (ev e (↓ (ext ρ x a) (fv e)) (⊔ σ a v) (φ ...))
        β
        (where a (alloc-cm ς))]))

(define-metafunction CM
  alloc-cm : ς -> a
  [(alloc-cm (co κ v ([a ↦ _] ...)))
   ,(+ 1 (apply max -1
                (filter integer?
                        (term (a ...)))))])

(define-metafunction CM
  inj-cm : e -> ς
  [(inj-cm e) (ev e () () (()))])

;; Set of free variables of an expression
(define-metafunction CM
  fv-cm : e -> any
  [(fv-cm x) ,(set (term x))]
  [(fv-cm (App e_1 e_2))
   (∪ (fv e_1) (fv e_2))]
  [(fv-cm (Lam x e))
   ,(set-remove (term (fv e)) (term x))]
  [(fv-cm (Frame R e)) (fv e)]
  [(fv-cm (Grant R e)) (fv e)]
  [(fv-cm (Test R e_0 e_1)) (∪ (fv e_0) (fv e_1))]
  [(fv-cm Fail) ∅])

(define-metafunction CM
  cont-update : κ R gn -> κ
  [(cont-update (m) R gn) ((marks-update m R gn))]
  [(cont-update ((AppL e ρ m) φ ...) R gn)
   ((AppL e ρ (marks-update m R gn)) φ ...)]
  [(cont-update ((AppR v m) φ ...) R gn)
   ((AppR v (marks-update m R gn)) φ ...)])

(define-metafunction CM
  marks-update : m R gn -> m
  [(marks-update m () gn) m]
  [(marks-update m (r_0 r_1 ...) gn)
   (marks-update (mark-update m r_0 gn) (r_1 ...) gn)])

(define-metafunction CM
  mark-update : m r gn -> m
  [(mark-update () r gn) ((r ↦ gn))]
  [(mark-update ([r ↦ gn_0] any_rest ...) r gn)
   ([r ↦ gn] any_rest ...)]
  [(mark-update (any_0 any_1 ...) r gn)
   (any_0 any_2 ...)
   (where (any_2 ...) (mark-update (any_1 ...) r gn))])

(define-metafunction CM
  ∧ : any any -> #t or #f
  [(∧ any_0 any_1) ,(and (term any_0) (term any_1))])

(define-metafunction CM
  ∩ : (any ...) (any ...) -> (any ...)
  [(∩ any_1 any_2)
   ,(set->list (set-intersect (list->set (term any_1))
                              (list->set (term any_2))))])

(define-metafunction CM
  ∅? : any -> #t or #f
  [(∅? ()) #t]
  [(∅? any) #f])

(term (∩ (a b c) (b c d)))
(term (∅? (∩ (a b) (c d))))
(term (∅? (∩ (a c) (c d))))

(define-metafunction CM
  inv-lookup : m gn -> R
  [(inv-lookup () gn) ()]
  [(inv-lookup ([r ↦ gn] [r_1 ↦ gn_1] ...) gn)
   (r r_2 ...)
   (where (r_2 ...) (inv-lookup ([r_1 ↦ gn_1] ...) gn))]
  [(inv-lookup ([r_0 ↦ gn_0] [r_1 ↦ gn_1] ...) gn)
   (inv-lookup ([r_1 ↦ gn_1] ...) gn)])

(test-equal (term (inv-lookup ([a ↦ no]) no)) (term (a)))
(test-equal (term (inv-lookup ([a ↦ no]) grant)) (term ()))

(define-metafunction CM
  OK : R κ -> #t or #f
  [(OK () κ) #t]
  [(OK R (m)) (∅? (∩ (inv-lookup m no) R))]
  [(OK R ((AppL e ρ m) φ ...))
   (∧ (∅? (∩ (inv-lookup m no) R))
      (OK R (φ ...)))]
  [(OK R ((AppR v m) φ ...))
   (∧ (∅? (∩ (inv-lookup m no) R))
      (OK R (φ ...)))])


;; Added component ι = stack of continuations
(define-extended-language CMι CM
  ;; Machine states
  [ς (ev e ρ σ κ ι)
     (co κ ι v σ)
     (ans v σ)]  
  ;; Meta continuations
  [ι (κ ...)])

;; Abstract machine in eval/apply form
;; with heap-allocated stack frames
(define -->_cmι
  (reduction-relation
   CMι
   #:domain ς
   ;; Eval transitions
   [--> (ev x ρ σ κ ι) (co κ ι v σ)
        Var
        (where (_ ... v _ ...) (lookup σ (lookup ρ x)))]
   [--> (ev (App e_0 e_1) ρ σ (φ ...) ι)
        (ev e_0 (↓ ρ (fv e_0)) σ ((AppL e_1 (↓ ρ (fv e_1)) ()) φ ...) ι)
        AppL]
   [--> (ev (Lam x e) ρ σ κ ι)
        (co κ ι (Clos x e (↓ ρ (fv e))) σ)
        Lam]

   ;; Stack inspection transitions
   [--> (ev (Frame R e) ρ σ κ ι)
        (ev e ρ σ (cont-update κ (complement R) no) ι)
        Frame]
   [--> (ev (Grant R e) ρ σ κ ι)
        (ev e ρ σ (cont-update κ R grant) ι)
        Grant]   
   [--> (ev (Test R e_0 e_1) ρ σ κ ι)
        (ev e_0 ρ σ κ ι)
        (where #t (OKι R κ ι))
        OK]
   [--> (ev (Test R e_0 e_1) ρ σ κ ι)
        (ev e_1 ρ σ κ ι)
        (where #f (OKι R κ ι))
        Not-OK]
   
   ;; Continue transitions
   ;; When local and meta contination are empty, evaluation is done
   [--> (co (m) () v σ) (ans v σ) Halt]
   ;; When local continuation is empty, install top continuation
   ;; in metacontinuation
   [--> (co () (κ_0 κ_1 ...) v σ) (co κ_0 (κ_1 ...) v σ) Return]
   
   [--> (co ((AppL e ρ m) φ ...) ι v σ)
        (ev e ρ σ ((AppR v ()) φ ...) ι)
        AppR]
   
   ;; Install an empty local continuation, push current local contination
   ;; to metacontinuation
   [--> (name ς (co ((AppR (Clos x e ρ) m) φ ...) (κ ...) v σ))
        (ev e (↓ (ext ρ x a) (fv e)) (⊔ σ a v) () ((φ ...) κ ...))
        β
        (where a (alloc-cmι ς))]))


(define-metafunction CMι
  OKι : R κ ι -> #t or #f
  [(OKι () κ ι) #t]
  [(OKι R () (κ_1 κ_2 ...))
   (OKι R κ_1 (κ_2 ...))]
  [(OKι R (m) ()) (∅? (∩ (inv-lookup m no) R))]
  [(OKι R ((AppL e ρ m) φ ...) ι)
   (∧ (∅? (∩ (inv-lookup m no) R))
      (OKι R (φ ...) ι))]
  [(OKι R ((AppR v m) φ ...) ι)
   (∧ (∅? (∩ (inv-lookup m no) R))
      (OKι R (φ ...) ι))])


(define-metafunction CMι
  alloc-cmι : ς -> a
  [(alloc-cmι (co κ v ([a ↦ _] ...)))
   ,(+ 1 (apply max -1
                (filter integer?
                        (term (a ...)))))])

(define-metafunction CMι
  inj-cmι : e -> ς
  [(inj-cmι e) (ev e () () (()) ())])

#;
(term (cont-update (([a ↦ grant])) (a b c) no))
#;
(traces -->_cm
        (term (inj-cm (App (Lam f (App (App f f) (Lam y y)))
                           (Lam x x)))))
#;
(traces -->_cm
        (term (inj-cm (Grant (a b) (Lam x x)))))

(traces -->_cmι
        (term (inj-cmι (Grant (a) (Test (a) (Lam one one) (Lam two two))))))

(traces -->_cmι
        (term (inj-cmι (Frame () (Test (a) (Lam one one) (Lam two two))))))

(traces -->_cmι
        (term (inj-cmι (Test (a) (Lam one one) (Lam two two)))))
