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
  [σ ([a ↦ s] ...)]
  ;; Storables
  [s v]
  ;; Continuations
  [κ Mt (AppL e ρ κ) (AppR v κ)]
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
   [--> (ev (App e_0 e_1) ρ σ κ)
        (ev e_0 ρ σ (AppL e_1 ρ κ))
        AppL]
   [--> (ev (Lam x e) ρ σ κ)
        (co κ (Clos x e ρ) σ)
        Lam]
   ;; Continue transitions
   [--> (co Mt v σ) (ans v σ) Halt]
   [--> (co (AppL e ρ κ) v σ)
        (ev e ρ σ (AppR v κ))
        AppR]
   [--> (name ς (co (AppR (Clos x e ρ) κ) v σ))
        (ev e (ext ρ x a) (ext σ a v) κ)
        β
        (where a (alloc ς))]))
 
(define-metafunction L
  inj : e -> ς
  [(inj e) (ev e () () Mt)])
 
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
  [(alloc (ev x ρ ([a ↦ _] ...) κ))
   ,(+ 1 (apply max -1
                (filter integer?
                        (term (a ...)))))]
  #;
  [(alloc (co κ v ([a ↦ _] ...)))
   ,(+ 1 (apply max -1
                (filter integer?
                        (term (a ...)))))])
 
(define-extended-language L* L
  [κ Mt (AppL e ρ a) (AppR v a)]
  [s .... κ])
 
;; Abstract machine in eval/apply form
;; with heap-allocated stack frames
(define -->_m*
  (reduction-relation
   L*
   #:domain ς
   ;; Eval transitions
   [--> (ev x ρ σ κ) (co κ v σ)
        Var
        (where v (lookup σ (lookup ρ x)))]
   [--> (name ς (ev (App e_0 e_1) ρ σ κ))
        (ev e_0 ρ (ext σ a κ) (AppL e_1 ρ a))
        (where a (alloc* ς))
        AppL]
   [--> (ev (Lam x e) ρ σ κ)
        (co κ (Clos x e ρ) σ)
        Lam]
   ;; Continue transitions
   [--> (co Mt v σ) (ans v σ) Halt]
   [--> (co (AppL e ρ a) v σ)
        (ev e ρ σ (AppR v a))
        AppR]
   [--> (co (AppR (Clos x e ρ) b) v σ)
        (ev e (ext ρ x a) (ext σ a v) κ)
        β
        (where a (alloc* ς))
        (where κ (lookup σ b))]))

(define-metafunction/extension alloc L*
  alloc* : ς -> a
  [(alloc* (ev (App e_0 e_1) ρ ([a ↦ _] ...) κ))
   ,(+ 1 (apply max -1
                (filter integer?
                        (term (a ...)))))])
 
(define (ev* e)
  (apply-reduction-relation* -->_m* (term (inj ,e))))
 
;; Visualize machine with stack allocated
(define (viz* e)
  (traces -->_m* (term (inj ,e))))
 
(define-extended-language L^ L*
  [σ ([a ↦ (s ...)] ...)])
 
(define-metafunction L^
  ⊔ : σ a s -> σ
  [(⊔ (name σ (any_1 ... [a ↦ (_ ... s_i _ ...)] any_2 ...)) a s_i)
   σ]
  [(⊔ (any_1 ... [a ↦ (s ...)] any_2 ...) a s_i)
   (any_1 ... [a ↦ (s ... s_i)] any_2 ...)]
  [(⊔ (any ...) a s) (any ... [a ↦ {s}])])
 
 
;; Swap these out for different abstractions
#;
;; constant allocation
(define-metafunction L^
  alloc^ : ς -> a
  [(alloc^ _) 0])
 
;; 0CFA-like abstraction
(define-metafunction L^
  alloc^ : ς -> a
  [(alloc^ (ev e ρ σ κ)) e]
  [(alloc^ (co (AppR (Clos x e ρ) b) v σ)) x])
 
 
;; Approximating Abstract machine in eval/apply form
;; with heap-allocated stack frames
(define -->_m^
  (reduction-relation
   L^
   #:domain ς
   ;; Eval transitions
   [--> (ev x ρ σ κ) (co κ v σ)
        Var
        (where (_ ... v _ ...) (lookup σ (lookup ρ x)))]
   [--> (name ς (ev (App e_0 e_1) ρ σ κ))
        (ev e_0 ρ (⊔ σ a κ) (AppL e_1 ρ a))
        (where a (alloc^ ς))
        AppL]
   [--> (ev (Lam x e) ρ σ κ)
        (co κ (Clos x e ρ) σ)
        Lam]
   ;; Continue transitions
   [--> (co Mt v σ) (ans v σ) Halt]
   [--> (co (AppL e ρ a) v σ)
        (ev e ρ σ (AppR v a))
        AppR]
   [--> (name ς (co (AppR (Clos x e ρ) b) v σ))
        (ev e (ext ρ x a) (⊔ σ a v) κ)
        β
        (where a (alloc^ ς))
        (where (_ ... κ _ ...) (lookup σ b))]))
 
(define (ev^ e)
  (apply-reduction-relation -->_m^ (term (inj ,e))))
 
;; visualize approximating machine
(define (viz^ e)
  (traces -->_m^ (term (inj ,e))))
 
 
;; Some examples
; (viz^ '(App (Lam x x) (Lam y y)))
; (viz^ '(App (Lam x (App x x)) (Lam y (App y y))))
; (viz^ '(App (Lam f (App (App f f) (Lam x x))) (Lam y y)))