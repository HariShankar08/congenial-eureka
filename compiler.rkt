#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp-Lif.rkt")
(require "interp.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "type-check-Lif.rkt")
(require "utilities.rkt")
(require graph)
(require "multigraph.rkt")
(require "priority_queue.rkt")
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
      [(Bool b) (Bool b)]
      [(Let x e body)
       (define new-x (gensym x))
       (define new-e ((uniquify-exp env) e))
       (define new-env (dict-set env x new-x))
       (define new-body ((uniquify-exp new-env) body))
       
       (Let new-x new-e new-body)
       ]
      [(If cnd thn els)
       (If ((uniquify-exp env) cnd)
           ((uniquify-exp env) thn)
           ((uniquify-exp env) els))] 
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : Lvar -> Lvar
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

;; remove-complex-opera* : Lvar -> Lvar^mon

(define (rco-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Void) (Void)]
    [(GlobalValue x) (GlobalValue x)]
    [(Allocate len t) (Allocate len t)]
    [(Collect bytes) (Collect bytes)]
    [(HasType e t) (HasType (rco-exp e) t)]
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
       (Let lhs rhs body))]
    [(If cnd thn els) 
     (If (rco-exp cnd) (rco-exp thn) (rco-exp els))]
    [(SetBang x rhs) 
     (SetBang x (rco-exp rhs))]
    [(GetBang x) 
     (GetBang x)]
    [(Begin es body) 
     (Begin (for/list ([e es]) (rco-exp e)) (rco-exp body))]
    [(WhileLoop cnd body) 
     (WhileLoop (rco-exp cnd) (rco-exp body))]))

(define (rco-atom e)
  (match e
    [(Var x) (values (Var x) '())]
    [(Int n) (values (Int n) '())]
    [(Bool b) (values (Bool b) '())]
    [(Void) (values (Void) '())]
    [(GlobalValue x) (values (GlobalValue x) '())]
    [else
     (define tmp (gensym 'tmp))
     (define new-e (rco-exp e))
     (values (Var tmp) (list (cons tmp new-e)))]))

(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (rco-exp e))]))

;; explicate-control : Lvar^mon -> Cvar
(define (explicate_effect e cont)
  (match e
    [(Var x) cont]
    [(Int n) cont]
    [(Bool b) cont]
    [(Void) cont]
    [(Collect bytes) (Seq (Collect bytes) cont)]
    [(Prim 'vector-set! es) (Seq (Prim 'vector-set! es) cont)]
    [(HasType e t) (explicate_effect e cont)]
    [(Let x rhs body) 
     (explicate_assign rhs x (explicate_effect body cont))]
    [(If cnd thn els) 
     (explicate_pred cnd (explicate_effect thn cont) (explicate_effect els cont))]
    [(Prim op es) cont]
    [(SetBang x rhs) 
     (explicate_assign rhs x cont)]
    [(Begin es body)
     (foldr (lambda (expr c) (explicate_effect expr c))
            (explicate_effect body cont)
            es)]
    [(WhileLoop cnd body)
     (define loop-label (gensym 'loop))
     (define loop-cont (Goto loop-label))
     (set! global-blocks 
           (dict-set global-blocks loop-label
                     (explicate_pred cnd (explicate_effect body loop-cont) cont)))
     loop-cont]
    [else (error "explicate_effect unhandled case" e)]))

(define (explicate_tail e) 
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Bool b) (Return (Bool b))] 
    [(Void) (Return (Void))]
    [(Prim op es) (Return (Prim op es))]
    [(Let x rhs body) (explicate_assign rhs x (explicate_tail body))]
    [(If cnd thn els) 
     (explicate_pred cnd (explicate_tail thn) (explicate_tail els))]
    [(SetBang x rhs) 
     (explicate_assign rhs x (Return (Void)))]
    [(Begin es body)
     (foldr (lambda (expr c) (explicate_effect expr c))
            (explicate_tail body)
            es)]
    [(WhileLoop cnd body)
     (define loop-label (gensym 'loop))
     (define loop-cont (Goto loop-label))
     (set! global-blocks 
           (dict-set global-blocks loop-label
                     (explicate_pred cnd (explicate_effect body loop-cont) (Return (Void)))))
     loop-cont]
    [else (error "explicate_tail unhandled case" e)]))

(define (explicate_assign e x cont) 
  (match e
    [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Bool b) (Seq (Assign (Var x) (Bool b)) cont)]
    [(Allocate len t) (Seq (Assign (Var x) (Allocate len t)) cont)]
    [(GlobalValue n) (Seq (Assign (Var x) (GlobalValue n)) cont)]
    [(HasType e t) (explicate_assign e x cont)]
    [(Void) (Seq (Assign (Var x) (Void)) cont)]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
    [(Let y rhs body) (explicate_assign rhs y (explicate_assign body x cont))]
    [(If cnd thn els) 
     (explicate_pred cnd 
                     (explicate_assign thn x cont) 
                     (explicate_assign els x cont))]
    [(SetBang y rhs)
     (explicate_assign rhs y (Seq (Assign (Var x) (Void)) cont))]
    [(Begin es body)
     (foldr (lambda (expr c) (explicate_effect expr c))
            (explicate_assign body x cont)
            es)]
    [(WhileLoop cnd body)
     (define loop-label (gensym 'loop))
     (define loop-cont (Goto loop-label))
     (set! global-blocks 
           (dict-set global-blocks loop-label
                     (explicate_pred cnd (explicate_effect body loop-cont) (Seq (Assign (Var x) (Void)) cont))))
     loop-cont]
    [else (error "explicate_assign unhandled case" e)]))

(define (explicate_pred cnd thn els)
  (match cnd
    [(Var x) (IfStmt (Prim 'eq? (list (Var x) (Bool #t))) 
                     (create_block thn) 
                     (create_block els))]
    [(Bool b) (if b thn els)]
    [(Let x rhs body) (explicate_assign rhs x (explicate_pred body thn els))]
    [(Prim 'not (list e)) (explicate_pred e els thn)]
    [(Prim op es) #:when (or (eq? op 'eq?) (eq? op '<) (eq? op '<=) (eq? op '>) (eq? op '>=))
     (IfStmt (Prim op es) (create_block thn) (create_block els))]
    [(If cnd^ thn^ els^) 
     (explicate_pred cnd^ 
                     (explicate_pred thn^ thn els) 
                     (explicate_pred els^ thn els))]
    [(Begin es body)
     (foldr (lambda (expr c) (explicate_effect expr c))
            (explicate_pred body thn els)
            es)]
    [else (error "explicate_pred unhandled case" cnd)]))

;; This needs to be defined within explicate-control or have access to a block dictionary
(define (create_block tail)
  (match tail
    [(Goto label) label]
    [else
     (define label (gensym 'block))
     (set! global-blocks (dict-set global-blocks label (Block '() tail)))
     (Goto label)]
  )
)
(define global-blocks '())

(define (explicate-control p)
  (match p
    [(Program info e) 
     (set! global-blocks '())
     (define tail (explicate_tail e))
     (define blocks (dict-set global-blocks 'start tail))
     (CProgram info blocks)]
  )
)
  
;; select-instructions : Cvar -> x86var
(define (select-instructions p)
  (match p
    [(CProgram info blocks)
     (define new-blocks
       (for/list ([(label tail) (in-dict blocks)])
         (cons label (Block '() (select-instr-tail tail)))))
     (X86Program info new-blocks)]))

(define (op->cc op)
  (match op
    ['eq? 'e]
    ['<   'l]
    ['<=  'le]
    ['>   'g]
    ['>=  'ge]
    [else (error "op->cc unhandled operator" op)]))

(define (select-instr-tail t)
  (match t
    [(Return e)
     (append (select-instr-exp e (Reg 'rax))
             (list (Jmp 'conclusion)))]
    [(Seq stmt tail)
     (append (select-instr-stmt stmt)
             (select-instr-tail tail))]
    [(Goto label) (list (Jmp label))]
    [(IfStmt (Prim op (list e1 e2)) (Goto thn) (Goto els))
     (list (Instr 'cmpq (list (select-atom e2) (select-atom e1)))
           (JmpIf (op->cc op) thn)
           (Jmp els))]
    [else (error "select-instr-tail unhandled case" t)]
  )
)

(define (select-instr-stmt s)
  (match s
    [(Assign (Var x) e)
     (select-instr-exp e (Var x))]
    [(Prim 'vector-set! (list e1 (Int i) e2))
     (list (Instr 'movq (list (select-atom e1) (Reg 'r11)))
           (Instr 'movq (list (select-atom e2) (Deref 'r11 (* 8 (add1 i))))))]
    [(Collect bytes)
     ;; The C runtime's collect() takes rootstack_ptr in %rdi and bytes in %rsi
     (list (Instr 'movq (list (Reg 'r15) (Reg 'rdi)))
           (Instr 'movq (list (Imm bytes) (Reg 'rsi)))
           (Instr 'callq (list 'collect)))]
    [else (error "select-instr-stmt unhandled case" s)]))

(define (select-instr-exp e dest)
  (match e
    [(Int n) (list (Instr 'movq (list (Imm n) dest)))]
    [(Var x) (list (Instr 'movq (list (Var x) dest)))]
    [(Bool #t) (list (Instr 'movq (list (Imm 1) dest)))]
    [(Bool #f) (list (Instr 'movq (list (Imm 0) dest)))]
    [(Void) '()] 
    [(GlobalValue name)
     (list (Instr 'movq (list (Global name) dest)))]
    [(Allocate len type)
     ;; tag = (length << 1) | 1
     (define tag (bitwise-ior (arithmetic-shift len 1) 1))
     (list
      (Instr 'movq (list (Global 'free_ptr) (Reg 'r11)))
      (Instr 'addq (list (Imm (+ 8 (* 8 len))) (Global 'free_ptr)))
      (Instr 'movq (list (Imm tag) (Deref 'r11 0)))
      (Instr 'movq (list (Reg 'r11) dest)))]
    [(Prim 'read '()) 
     (list (Instr 'callq (list 'read_int))
           (Instr 'movq (list (Reg 'rax) dest)))]
    [(Prim '+ (list e1 e2))
     (list (Instr 'movq (list (select-atom e1) dest))
           (Instr 'addq (list (select-atom e2) dest)))]
    [(Prim '- (list e1))
     (list (Instr 'movq (list (select-atom e1) dest))
           (Instr 'negq (list dest)))]
    [(Prim op (list e1 e2)) #:when (set-member? '(< <= > >= eq?) op)
     (list (Instr 'cmpq (list (select-atom e2) (select-atom e1)))
           (Instr 'set (list (op->cc op) (ByteReg 'al)))
           (Instr 'movzbq (list (ByteReg 'al) dest)))]
    [(Prim 'vector-ref (list e1 (Int i)))
     (list (Instr 'movq (list (select-atom e1) (Reg 'r11)))
           (Instr 'movq (list (Deref 'r11 (* 8 (add1 i))) dest)))]
    [else (error "select-instr-exp unhandled case" e)]))



(define (select-atom a)
  (match a
    [(Int n) (Imm n)]
    [(Var x) (Var x)]
    [(Bool #t) (Imm 1)]
    [(Bool #f) (Imm 0)]
    [(Void) (Imm 0)] ; We can treat Void as 0 in contexts where an atom is needed
    [else (error "select-atom unhandled case" a)]
  )
)


    
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

;; Helper for Pass 8 (Updated for Exercise 3.5)
;; Ensures at most one memory access per instruction and deletes trivial moves.
(define (patch-instr-helper i)
  (match i
    ;; Delete trivial moves where source and destination are the same
    [(Instr 'movq (list src dest)) #:when (equal? src dest)
     '()]
    
    ;; cmpq: second argument must NOT be an immediate. Handle immediates
    ;; by moving the immediate into `rax` and comparing against that.
    [(Instr 'cmpq (list (Imm n1) (Imm n2)))
     (list (Instr 'movq (list (Imm n2) (Reg 'rax)))
       (Instr 'cmpq (list (Imm n1) (Reg 'rax))))]

    [(Instr 'cmpq (list src (Imm n)))
     (list (Instr 'movq (list (Imm n) (Reg 'rax)))
       (Instr 'cmpq (list src (Reg 'rax))))]

    ;; movzbq: destination must be a register. If it's memory, move via rax.
    [(Instr 'movzbq (list src dest))
     (match dest
   [(Reg r) (list i)]
   [else (list (Instr 'movzbq (list src (Reg 'rax)))
       (Instr 'movq (list (Reg 'rax) dest)))])]

    ;; Fix instructions with two memory accesses: move first memory to rax.
    [(Instr op (list (Deref r1 o1) (Deref r2 o2)))
     (list (Instr 'movq (list (Deref r1 o1) (Reg 'rax)))
       (Instr op (list (Reg 'rax) (Deref r2 o2))))]

    ;; Keep all other instructions as-is
    [else (list i)]))

;; Main patch-instructions pass
(define (patch-instructions p)
  (match p
    [(X86Program info blocks)
     (define new-blocks
       (for/list ([(label block) (in-dict blocks)])
         (match block
           [(Block b-info instrs)
            (cons label (Block b-info (append-map patch-instr-helper instrs)))])))
     (X86Program info new-blocks)]))


;; Helper: Generate push instructions for used callee-saved registers
(define (make-pushes regs)
  (for/list ([r regs])
    (Instr 'pushq (list (Reg r)))))

;; Helper: Generate pop instructions for used callee-saved registers (reverse order)
(define (make-pops regs)
  (for/list ([r (reverse regs)])
    (Instr 'popq (list (Reg r)))))

(define (prelude-and-conclusion p)
  (match p
    [(X86Program info blocks)
     (define used-callee (dict-ref info 'used-callee '()))
     (define num-callee (length used-callee))
     (define num-spills (/ (dict-ref info 'stack-space 0) 8))
     (define num-root-spills (dict-ref info 'num-root-spills 0))
     
     (define ss-total (align (+ (* 8 num-spills) (* 8 num-callee)) 16))
     (define stack-adj (- ss-total (* 8 num-callee)))
     
     (define main-prelude
       (append
        (list (Instr 'pushq (list (Reg 'rbp)))
              (Instr 'movq (list (Reg 'rsp) (Reg 'rbp))))
        (make-pushes used-callee)
        (if (zero? stack-adj) '() (list (Instr 'subq (list (Imm stack-adj) (Reg 'rsp)))))
        
        ;; GC Initialization (16,384 bytes for rootstack and heap)
        (list (Instr 'movq (list (Imm 16384) (Reg 'rdi)))
              (Instr 'movq (list (Imm 16384) (Reg 'rsi)))
              (Instr 'callq (list 'initialize))
              ;; Initialize the root stack pointer (%r15)
              (Instr 'movq (list (Global 'rootstack_begin) (Reg 'r15))))
              
        ;; Zero out root stack slots
        (for/list ([i (in-range 1 (add1 num-root-spills))])
          (Instr 'movq (list (Imm 0) (Deref 'r15 (* -8 i)))))
          
        ;; Advance root stack pointer past the spilled variables
        (if (zero? num-root-spills) 
            '() 
            (list (Instr 'addq (list (Imm (* 8 num-root-spills)) (Reg 'r15)))))
            
        (list (Jmp 'start))))
     
     (define conclusion
       (append
        ;; Return root stack pointer back down
        (if (zero? num-root-spills) 
            '() 
            (list (Instr 'subq (list (Imm (* 8 num-root-spills)) (Reg 'r15)))))
        (if (zero? stack-adj) '() (list (Instr 'addq (list (Imm stack-adj) (Reg 'rsp)))))
        (make-pops used-callee)
        (list (Instr 'popq (list (Reg 'rbp)))
              (Retq))))
     
     (define new-blocks
       (append (list (cons 'main (Block '() main-prelude))
                     (cons 'conclusion (Block '() conclusion)))
               blocks))
     (X86Program info new-blocks)]))


;; uncover-live : x86var -> x86var
(define (uncover-live p)
  (match p
    [(X86Program info blocks)
     (define block-instrs
       (for/hash ([(label block) (in-dict blocks)])
         (match block
           [(Block _ instrs)
            (define instrs-list
              (cond
                [(and (pair? instrs) (or (Instr? (car instrs)) (Jmp? (car instrs)) (JmpIf? (car instrs)) (Retq? (car instrs))))
                 instrs]
                [(list? instrs) instrs]
                [else (select-instr-tail instrs)]))
            (values label instrs-list)])))
     
     (define live-before-map (make-hash))
     (for ([(label _) (in-dict blocks)]) (hash-set! live-before-map label (set)))
     
     ;; Graph edges for worklist (predecessors mapping)
     (define preds-map (make-hash))
     (for ([(label instrs) (in-hash block-instrs)])
       (for ([i (in-list instrs)] #:when (or (Jmp? i) (JmpIf? i)))
         (define t (match i [(Jmp tgt) tgt] [(JmpIf cc tgt) tgt]))
         (hash-set! preds-map t (set-add (hash-ref preds-map t (set)) label))))
     
     (define worklist (map car (dict->list blocks)))
     
     (let loop ()
       (unless (null? worklist)
         (define label (car worklist))
         (set! worklist (cdr worklist))
         
         (define instrs (hash-ref block-instrs label))
         (define live-before
           (for/fold ([live-after (set)]) ([instr (in-list (reverse instrs))])
             (compute-live-before instr live-after live-before-map)))
         
         (define old-live-before (hash-ref live-before-map label))
         (unless (equal? live-before old-live-before)
           (hash-set! live-before-map label live-before)
           (set! worklist (append (set->list (hash-ref preds-map label (set))) worklist)))
         (loop)))
         
     (define new-blocks
       (for/list ([(label block) (in-dict blocks)])
         (define instrs (hash-ref block-instrs label))
         (define b-info (match block [(Block i _) i]))
         
         (define-values (new-instrs final-live live-sets)
           (for/fold ([acc-instrs '()]
                      [live-after (set)]
                      [acc-live-sets '()])
                     ([instr (in-list (reverse instrs))])
             (let* ([instr-live-after live-after]
                    [live-before (compute-live-before instr live-after live-before-map)])
               (values (cons instr acc-instrs)
                       live-before
                       (cons instr-live-after acc-live-sets)))))
         
         (cons label (Block (dict-set (dict-set b-info 'live-after final-live)
                                      'live-after-sets live-sets)
                            new-instrs))))
     (X86Program info new-blocks)]))

;; Helper to extract variables/registers from an instruction's arguments
(define (get-vars arg)
  (match arg
    [(Var x) (set x)]
    [(Reg r) (set r)]
    [(ByteReg r)
     (set (match r
            ['ah 'rax] ['al 'rax]
            ['bh 'rbx] ['bl 'rbx]
            ['ch 'rcx] ['cl 'rcx]
            ['dh 'rdx] ['dl 'rdx]
            [else r]))]
    [else (set)]))

;; Logic to determine what variables an instruction defines (def) and uses (use)
(define (compute-live-before instr live-after live-before-map)
  (match instr
    [(Instr 'movq (list src dest))
     (set-union (set-remove live-after (get-vars dest)) (get-vars src))]
    [(Instr 'movzbq (list src dest))
     (set-union (set-remove live-after (get-vars dest)) (get-vars src))]
    [(Instr op (list src dest)) #:when (set-member? '(addq subq xorq) op)
     (set-union (set-remove live-after (get-vars dest)) 
                (get-vars src) (get-vars dest))]
    [(Instr 'cmpq (list src dest))
     (set-union live-after (get-vars src) (get-vars dest))]
    [(Instr 'negq (list dest))
     (set-union (set-remove live-after (get-vars dest)) (get-vars dest))]
    [(Instr 'set (list cc dest))
     (set-remove live-after (get-vars dest))]
    [(Instr 'pushq (list src))
     (set-union live-after (get-vars src))]
    [(Instr 'popq (list dest))
     (set-remove live-after (get-vars dest))]
    [(Instr 'callq (list target)) ;; Calls clobber caller-save registers
     (set-union (set-subtract live-after caller-save) (get-vars target))]
    [(Retq) (set-union live-after (set 'rax))] ;; Return uses rax
    [(Jmp target) 
     (hash-ref live-before-map target (set))]
    [(JmpIf cc target) 
     (set-union live-after (hash-ref live-before-map target (set)))]
    [else live-after]))

;; Helper for build-interference
;; Updates the interference graph based on an instruction and its live-after set
(define (build-interference-helper i live-after graph)
  (define (add-conflicts dests src-vars)
    (for ([v live-after])
      (for ([d dests])
        (unless (or (equal? v d) (and src-vars (set-member? src-vars v)))
          (add-edge! graph v d)))))
  
  (match i
    [(Instr 'movq (list src dest))
     (add-conflicts (get-vars dest) (get-vars src))]
    [(Instr 'movzbq (list src dest))
     (add-conflicts (get-vars dest) (get-vars src))]
    [(Instr 'cmpq (list src dest))
     (void)] ; cmpq defines no registers
    [(Instr op (list src dest))
     (add-conflicts (get-vars dest) #f)]
    [(Instr 'set (list cc dest))
     (add-conflicts (get-vars dest) #f)]
    [(Instr 'pushq (list src))
     (void)] ; pushq defines no registers
    [(Instr op (list dest))
     (add-conflicts (get-vars dest) #f)]
    [(Instr 'callq (list target))
     ;; After a call, all caller-save registers interfere with all live variables
     (for ([v live-after])
       (for ([r (set->list caller-save)])
         (unless (equal? v r)
           (add-edge! graph v r))))]
    [else (void)]))

(define (build-interference p)
  (match p
    [(X86Program info blocks)
     (define locals (map fst (dict-ref info 'locals-types '())))
     ;; Use undirected-graph from the 'graph' library
     (define g (undirected-graph '()))
     
     ;; Add vertices for all variables and general-purpose registers
     (for ([v (append locals (vector->list general-registers))])
       (add-vertex! g v))
     
     (for ([(label block) (in-dict blocks)])
       (match block
         [(Block b-info instrs)
          ;; Normalize instruction sequence: some blocks may contain
          ;; Lif-created tail forms instead of flat instruction lists.
          (define instr-list
            (cond
              [(and (pair? instrs)
                    (or (Instr? (car instrs)) (Jmp? (car instrs)) (JmpIf? (car instrs)) (Retq? (car instrs))))
               instrs]
              [(list? instrs) instrs]
              [else (select-instr-tail instrs)]))

          ;; Get per-instruction live-after sets if available; otherwise
          ;; fall back to the block-level live-after set produced by uncover-live.
          (define live-afters (dict-ref b-info 'live-after-sets '()))
          (define block-live (dict-ref b-info 'live-after (set)))
          (when (null? live-afters)
            (set! live-afters (for/list ([i (in-list instr-list)]) block-live)))

          ;; Ensure lists are the same length: pad/truncate as needed
          (define n-instr (length instr-list))
          (define n-live (length live-afters))
          (cond
            [(< n-live n-instr)
             (set! live-afters (append live-afters (make-list (- n-instr n-live) block-live)))]
            [(> n-live n-instr)
             (set! live-afters (take live-afters n-instr))])

          (for ([i instr-list] [la live-afters])
            (build-interference-helper i la g))]))
            
     (X86Program (dict-set info 'conflicts g) blocks)]))

;; Helper: Pick the smallest available color (non-negative integer)
(define (get-lowest-color neighbors coloring)
  (define neighbor-colors (for/set ([n neighbors] #:when (dict-has-key? coloring n))
                             (dict-ref coloring n)))
  (let loop ([c 0])
    (if (set-member? neighbor-colors c) (loop (add1 c)) c)))

(define (pointer-type? t)
  (match t
    [`(Vector ,_ ...) #t]
    [`(Vectorof ,_) #t]
    [else #f]))

(define (allocate-registers p)
  (match p
    [(X86Program info blocks)
     (define g (dict-ref info 'conflicts))
     (define locals-types (dict-ref info 'locals-types '()))
     (define vars (map fst locals-types))
     
     (define coloring (for/hash ([r (in-vertices g)] #:when (set-member? registers r))
                        (values r (register->color r))))
     
     (for ([v vars])
       (define color (get-lowest-color (get-neighbors g v) coloring))
       (set! coloring (hash-set coloring v color)))

     ;; Independent counters for dense stack packing
     (define next-root-spill 1)
     (define next-scalar-spill 1)
     (define color->spill-slot (make-hash))

     (define (color->arg c x)
       (if (and (>= c 0) (< c (num-registers-for-alloc)))
           (Reg (color->register c))
           (let ([type (dict-ref locals-types x 'Any)])
             (if (pointer-type? type)
                 (let ([slot (hash-ref! color->spill-slot c (lambda () 
                               (begin0 next-root-spill (set! next-root-spill (add1 next-root-spill)))))])
                   (Deref 'r15 (* -8 slot)))
                 (let ([slot (hash-ref! color->spill-slot c (lambda () 
                               (begin0 next-scalar-spill (set! next-scalar-spill (add1 next-scalar-spill)))))])
                   (Deref 'rbp (* -8 slot)))))))

     (define (assign-arg a)
       (match a [(Var x) (color->arg (hash-ref coloring x) x)] [else a]))

     (define (assign-instr i)
       (match i [(Instr op args) (Instr op (map assign-arg args))] [else i]))

     (define new-blocks
       (for/list ([(label block) (in-dict blocks)])
         (match block [(Block b-info instrs) 
                       (cons label (Block b-info (map assign-instr instrs)))])))
     
     (define used-callee 
        (for/set ([color (hash-values coloring)]
            #:when (and (>= color 0) (< color (num-registers-for-alloc))))
            (color->register color)))

      (define used-callee-list 
        (set->list (set-intersect used-callee callee-save)))
      
      (define num-spills (sub1 next-scalar-spill))
      (define num-root-spills (sub1 next-root-spill))

      (X86Program (dict-set 
                    (dict-set 
                      (dict-set info 'stack-space (* 8 num-spills)) 
                      'num-root-spills num-root-spills)
                    'used-callee used-callee-list) 
              new-blocks)]))


;; Lif passes
(define (shrink-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Void) (Void)]
    [(Let x rhs body)
     (Let x (shrink-exp rhs) (shrink-exp body))]
    [(If cnd thn els)
     (If (shrink-exp cnd) (shrink-exp thn) (shrink-exp els))]
    [(Prim 'and (list e1 e2))
     (If (shrink-exp e1) (shrink-exp e2) (Bool #f))]
    [(Prim 'or (list e1 e2))
     (If (shrink-exp e1) (Bool #t) (shrink-exp e2))]
    [(Prim op es)
     (Prim op (for/list ([e es]) (shrink-exp e)))]
    [(SetBang x rhs) 
     (SetBang x (shrink-exp rhs))]
    [(GetBang x) 
     (GetBang x)]
    [(Begin es body) 
     (Begin (for/list ([e es]) (shrink-exp e)) (shrink-exp body))]
    [(WhileLoop cnd body) 
     (WhileLoop (shrink-exp cnd) (shrink-exp body))]
    [else (error "shrink-exp unhandled case" e)]))

(define (shrink p)
  (match p
    [(Program info e) (Program info (shrink-exp e))]))

(define (expose-alloc-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Void) (Void)]
    [(Let x rhs body)
     (Let x (expose-alloc-exp rhs) (expose-alloc-exp body))]
    [(If cnd thn els)
     (If (expose-alloc-exp cnd) (expose-alloc-exp thn) (expose-alloc-exp els))]
    [(Begin es body)
     (Begin (map expose-alloc-exp es) (expose-alloc-exp body))]
    [(SetBang x rhs)
     (SetBang x (expose-alloc-exp rhs))]
    [(GetBang x)
     (GetBang x)]
    [(WhileLoop cnd body)
     (WhileLoop (expose-alloc-exp cnd) (expose-alloc-exp body))]
    [(HasType (Prim 'vector es) t)
     (define bytes (+ 8 (* 8 (length es)))) ; 8 bytes for tag + 8 per element
     (define void-var (gensym '_))
     (define tup-var (gensym 'alloc))
     (define new-es (map expose-alloc-exp es))
     
     ;; condition: free_ptr + bytes < fromspace_end
     (define cond-e
       (Prim '< (list (Prim '+ (list (GlobalValue 'free_ptr) (Int bytes)))
                      (GlobalValue 'fromspace_end))))
     
     ;; If not enough space, collect
     (define thn-e (Void))
     (define els-e (Collect bytes))
     
     ;; Allocate memory
     (define alloc-e (Allocate (length es) t))
     
     ;; Set the fields
     (define sets
       (for/list ([arg new-es] [i (in-naturals)])
         (Prim 'vector-set! (list (Var tup-var) (Int i) arg))))
     
     (HasType
      (Let void-var (If cond-e thn-e els-e)
           (Let tup-var alloc-e
                (if (null? sets)
                    (Var tup-var)
                    (Begin sets (Var tup-var)))))
      t)]
    [(HasType e t)
     (HasType (expose-alloc-exp e) t)]
    [(Prim op es)
     (Prim op (map expose-alloc-exp es))]
    [else (error "expose-alloc-exp unhandled case" e)]))

(define (expose-allocation p)
  (match p
    [(Program info e) (Program info (expose-alloc-exp e))]))




;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
     ("uniquify" ,uniquify ,interp_Lvar ,type-check-Lvar)
     ("shrink" ,shrink ,interp-Lif ,type-check-Lif)
     ("expose allocation" ,expose-allocation ,interp-Lvec ,type-check-Lvec)
     ("remove complex opera*" ,remove-complex-opera* ,interp_Lvar ,type-check-Lvar)
     ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
     ("instruction selection" ,select-instructions ,interp-pseudo-x86-0)
     ("uncover live" ,uncover-live ,interp-pseudo-x86-0)
     ("build interference" ,build-interference ,interp-pseudo-x86-0)
     ("allocate registers" ,allocate-registers ,interp-x86-0)
     ("patch instructions" ,patch-instructions ,interp-x86-0)
     ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))