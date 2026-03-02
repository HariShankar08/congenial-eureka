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

;; Helper for Pass 8 (Updated for Exercise 3.5)
;; Ensures at most one memory access per instruction and deletes trivial moves.
(define (patch-instr-helper i)
  (match i
    ;; Delete trivial moves where source and destination are the same
    [(Instr 'movq (list src dest)) #:when (equal? src dest)
     '()]
    
    ;; Fix instructions with two memory accesses
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
     
     ;; Calculate alignment: A = align(8S + 8C) - 8C
     (define ss-total (align (+ (* 8 num-spills) (* 8 num-callee)) 16))
     (define stack-adj (- ss-total (* 8 num-callee)))
     
     (define main-prelude
       (append
        (list (Instr 'pushq (list (Reg 'rbp)))
              (Instr 'movq (list (Reg 'rsp) (Reg 'rbp))))
        (make-pushes used-callee)
        (if (zero? stack-adj) '() (list (Instr 'subq (list (Imm stack-adj) (Reg 'rsp)))))
        (list (Jmp 'start))))
     
     (define conclusion
       (append
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
     (X86Program info
       (for/list ([(label block) (in-dict blocks)])
         (cons label (uncover-live-block block))))]))

;; Performs liveness analysis on a single block (backward pass)
(define (uncover-live-block b)
  (match b
    [(Block info instrs)
     (define-values (new-instrs final-live)
       (for/fold ([acc-instrs '()]
                  [live-after (set)])
                 ([instr (reverse instrs)])
         (let* ([live-before (compute-live-before instr live-after)]
                ;; Store the liveness information in the instruction info
                [instr-with-live (add-live-to-instr instr live-after)])
           (values (cons instr-with-live acc-instrs) live-before))))
     (Block (dict-set info 'live-after final-live) new-instrs)]))

;; Helper to extract variables/registers from an instruction's arguments
(define (get-vars arg)
  (match arg
    [(Var x) (set x)]
    [(Reg r) (set r)]
    [else (set)]))

;; Logic to determine what variables an instruction defines (def) and uses (use)
(define (compute-live-before instr live-after)
  (match instr
    [(Instr 'movq (list src dest))
     (set-union (set-remove live-after (get-vars dest)) (get-vars src))]
    [(Instr op (list src dest)) ;; For addq, subq, etc. (dest = dest op src)
     (set-union (set-remove live-after (get-vars dest)) 
                (get-vars src) (get-vars dest))]
    [(Instr 'negq (list dest))
     (set-union (set-remove live-after (get-vars dest)) (get-vars dest))]
    [(Instr 'callq (list target)) ;; Calls clobber caller-save registers
     (set-union (set-subtract live-after caller-save) (get-vars target))]
    [(Retq) (set 'rax)] ;; Return uses rax
    [(Jmp target) live-after] ;; Standard jumps don't change liveness directly
    [else live-after]))

;; Simple wrapper to attach liveness info to instructions if your AST supports it
;; Otherwise, this can be stored in a side-table.
(define (add-live-to-instr instr live-set)
  ;; Depending on your project requirements, you might wrap this 
  ;; in a custom struct or just return the instr.
  instr)

;; Helper for build-interference
;; Updates the interference graph based on an instruction and its live-after set
(define (build-interference-helper i live-after graph)
  (match i
    [(Instr 'movq (list src dest))
     (for ([v live-after])
       (for ([d (get-vars dest)])
         ;; In movq s, d: d interferes with v if v != d AND v != s
         (unless (or (equal? v d) (equal? v (get-vars src)))
           (add-edge! graph v d))))]
    [(Instr op (list src dest))
     (for ([v live-after])
       (for ([d (get-vars dest)])
         (unless (equal? v d)
           (add-edge! graph v d))))]
    [(Instr op (list dest))
     (for ([v live-after])
       (for ([d (get-vars dest)])
         (unless (equal? v d)
           (add-edge! graph v d))))]
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
          ;; Ensure 'live-after-sets' exists in the block info from uncover-live
          (define live-afters (dict-ref b-info 'live-after-sets '()))
          (for ([i instrs] [la live-afters])
            (build-interference-helper i la g))]))
            
     (X86Program (dict-set info 'conflicts g) blocks)]))

;; Helper: Pick the smallest available color (non-negative integer)
(define (get-lowest-color neighbors coloring)
  (define neighbor-colors (for/set ([n neighbors] #:when (dict-has-key? coloring n))
                             (dict-ref coloring n)))
  (let loop ([c 0])
    (if (set-member? neighbor-colors c) (loop (add1 c)) c)))

(define (allocate-registers p)
  (match p
    [(X86Program info blocks)
     (define g (dict-ref info 'conflicts))
     (define vars (map fst (dict-ref info 'locals-types '())))
     ;; Pre-color registers based on their standard indices
     (define coloring (for/hash ([r (in-vertices g)] #:when (set-member? registers r))
                        (values r (register->color r))))
     
     ;; DSATUR coloring: we color variables greedily
     (for ([v vars])
       (define color (get-lowest-color (get-neighbors g v) coloring))
       (set! coloring (hash-set coloring v color)))

     ;; Map colors to specific locations (registers or stack)
     (define (color->arg c)
       (if (and (>= c 0) (< c (num-registers-for-alloc)))
           (Reg (color->register c))
           (Deref 'rbp (* -8 (- c (num-registers-for-alloc) -1)))))

     (define (assign-arg a)
       (match a [(Var x) (color->arg (hash-ref coloring x))] [else a]))

     (define (assign-instr i)
       (match i [(Instr op args) (Instr op (map assign-arg args))] [else i]))

     (define new-blocks
       (for/list ([(label block) (in-dict blocks)])
         (match block [(Block b-info instrs) 
                       (cons label (Block b-info (map assign-instr instrs)))])))
     
     ;; Update stack space in info for spills
     (define max-color (apply max -1 (hash-values coloring)))
     (define spills (max 0 (add1 (- max-color (num-registers-for-alloc)))))
     
     (define used-callee 
        (for/set ([color (hash-values coloring)]
            #:when (and (>= color 0) (< color (num-registers-for-alloc))))
            (color->register color)))

      (define used-callee-list 
        (set->list (set-intersect used-callee callee-save)))

      
      (X86Program (dict-set (dict-set info 'stack-space (* 8 spills)) 
                      'used-callee used-callee-list) 
              new-blocks)]))


;; Lif passes

;; shrink-exp : LIf -> LIf
(define (shrink-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
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
    [else (error "shrink-exp unhandled case" e)]))

(define (shrink p)
  (match p
    [(Program info e) (Program info (shrink-exp e))]))


;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
     ("uniquify",uniquify ,interp_Lvar ,type-check-Lvar)
     ("shrink" ,shrink ,interp-Lif ,type-check-Lif)
     ("remove complex opera*" ,remove-complex-opera* ,interp_Lvar ,type-check-Lvar)
     ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
     ("instruction selection" ,select-instructions ,interp-pseudo-x86-0)
     ("uncover live" ,uncover-live ,interp-pseudo-x86-0)
     ("build interference" ,build-interference ,interp-pseudo-x86-0)
     ("allocate registers" ,allocate-registers ,interp-x86-0)
     ("patch instructions" ,patch-instructions ,interp-x86-0)
     ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))