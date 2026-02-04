#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Lint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))


;; Next we have the partial evaluation pass described in the book.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]
    [(Prim '- (list e1 e2)) (pe-add (pe-exp e1) (pe-neg (pe-exp e2)))]
    ))

(define (pe-Lint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (Var (dict-ref env x x))]
      [(Int n) (Int n)]
      [(Let x e body)
       (define new-x (gensym x))
       (define new-e ((uniquify-exp env) e))
       (define new-env (dict-set env x new-x))
       (define new-body ((uniquify-exp new-env) body))
       
       (Let new-x new-e new-body)
       ]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : Lvar -> Lvar
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

;; remove-complex-opera* : Lvar -> Lvar^mon


(define (rco-atom e)
  (match e
  [(Var x) (values (Var x) '())]
  [(Int n) (values (Int n) '())]
  [else
    (define tmp (gensym 'tmp))
    (define new-e (rco-exp e))
    (values (Var tmp) (dict-set '() tmp new-e))]))

(define (rco-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Let x rhs body)
     (Let x (rco-exp rhs) (rco-exp body))]
    [(Prim op es)
     (define-values (atoms bindings-lists)
       (for/lists (n1 n2) ([arg es])
         (rco-atom arg)))
     
     (define all-bindings (apply append bindings-lists))
     (define core (Prim op atoms))
     
     (for/fold ([body core])
               ([(lhs rhs) (in-dict (reverse all-bindings))])
       (Let lhs rhs body))]))


(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (rco-exp e))]))
  
;; explicate-control : Lvar^mon -> Cvar

(define (explicate_tail e) 
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Prim op es) (Return (Prim op es))]
    [(Let x rhs body) (explicate_assign rhs x (explicate_tail body))]
    [else (error "explicate_tail unhandled case" e)])
)

(define (explicate_assign e x cont) 
  (match e
    [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
    [(Let y rhs body) (explicate_assign rhs y (explicate_assign body x cont))]
    
  )
)

(define (explicate-control p)
 (match p
    [(Program info e) 
      (define tail (explicate_tail e))
      (define blocks (dict-set '() 'start tail))
      (CProgram info blocks)
    ]))
  
;; select-instructions : Cvar -> x86var
(define (select-instructions p)
  (match p
    [(CProgram info blocks)
     (define new-blocks
       (for/list ([(label tail) (in-dict blocks)])
         (cons label (Block '() (select-instr-tail tail)))))
     (X86Program info new-blocks)]))

(define (select-instr-tail t)
  (match t
    [(Return e)
     (append (select-instr-exp e (Reg 'rax))
             (list (Jmp 'conclusion)))]
    [(Seq stmt tail)
     (append (select-instr-stmt stmt)
             (select-instr-tail tail))]
    [else (error "select-instr-tail unhandled case" t)]))

(define (select-instr-stmt s)
  (match s
    [(Assign (Var x) e)
     (select-instr-exp e (Var x))]))

(define (select-instr-exp e dest)
  (match e
    [(Int n) (list (Instr 'movq (list (Imm n) dest)))]
    [(Var x) (list (Instr 'movq (list (Var x) dest)))]
    [(Prim 'read '()) (list (Instr 'callq (list 'read_int))
                            (Instr 'movq (list (Reg 'rax) dest)))]
    [(Prim '+ (list e1 e2))
     (list (Instr 'movq (list (select-atom e1) dest))
           (Instr 'addq (list (select-atom e2) dest)))]
    [(Prim '- (list e1))
     (list (Instr 'movq (list (select-atom e1) dest))
           (Instr 'negq (list dest)))]))

(define (select-atom a)
  (match a
    [(Int n) (Imm n)]
    [(Var x) (Var x)]))
    
;; assign-homes : x86var -> x86var
(define (assign-homes p)
  (match p
    [(X86Program info blocks)
     (define vars (map fst (dict-ref info 'locals-types '())))
     (define home-map 
       (for/list ([v vars] [i (in-naturals 1)])
         (cons v (Deref 'rbp (* -8 i)))))
     (define (assign-arg a)
       (match a
         [(Var x) (dict-ref home-map x)]
         [else a]))
     (define (assign-instr i)
       (match i
         [(Instr op args) (Instr op (map assign-arg args))]
         [else i]))
     (define new-blocks
       (for/list ([(label block) (in-dict blocks)])
         (match block
           [(Block b-info instrs) 
            (cons label (Block b-info (map assign-instr instrs)))])))
     (X86Program (dict-set info 'stack-space (* 8 (length vars))) new-blocks)]))

;; patch-instructions : x86var -> x86int
(define (patch-instructions p)
  (match p
    [(X86Program info blocks)
     (define (patch-instr i)
       (match i
         [(Instr op (list (Deref r1 o1) (Deref r2 o2)))
          (list (Instr 'movq (list (Deref r1 o1) (Reg 'rax)))
                (Instr op (list (Reg 'rax) (Deref r2 o2))))]
         [else (list i)]))
     (define new-blocks
       (for/list ([(label block) (in-dict blocks)])
         (match block
           [(Block b-info instrs)
            (cons label (Block b-info (append-map patch-instr instrs)))])))
     (X86Program info new-blocks)]))


;; prelude-and-conclusion : x86int -> x86int
(define (prelude-and-conclusion p)
  (error "TODO: code goes here (prelude-and-conclusion)"))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
     ;; Uncomment the following passes as you finish them.
     ("uniquify" ,uniquify ,interp_Lvar ,type-check-Lvar)
     ("remove complex opera*" ,remove-complex-opera* ,interp_Lvar ,type-check-Lvar)
     ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
     ("instruction selection" ,select-instructions ,interp-pseudo-x86-0)
     ("assign homes" ,assign-homes ,interp-x86-0)
     ("patch instructions" ,patch-instructions ,interp-x86-0)
     ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))
