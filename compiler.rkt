#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Clambda.rkt")
(require "type-check-Clambda.rkt")
(require "type-check-Llambda.rkt")
(require "interp-Llambda.rkt")
(require "interp-Llambda-prime.rkt")
(require "interp-Lfun.rkt")
(require "type-check-Lfun.rkt")
(require "interp-Lfun-prime.rkt")
(require "interp-Cfun.rkt")
(require "type-check-Cfun.rkt")
(require "utilities.rkt")
(provide (all-defined-out))
(require "interp.rkt")
(require "priority_queue.rkt")
(require graph)
(require data/queue)
;;(system-type ’os)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Int n) e]
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
    [(Int n) e]
    [(Var n) e]
    [(Prim 'read '()) e]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]
    [(Let x e body) (Let x (pe-exp e) (pe-exp body))]))


(define (pe-Lvar p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;--------------------------------------------------------------------------------------;
;; Q11
;; Ints cannot be negative in this grammar hence pe-neg was not re-written to know more about arithmetic

(define (residual? e)
  (match e
    [(Int _) #t]
    [(Prim '+ `(,(Int _) ,e2)) (inert? e2)]
    [else (inert? e)]))

(define (inert? e)
  (match e
    [(Var _) #t]
    [(Prim 'read '()) #t]
    [(Prim '- `(,(Var _))) #t]
    [(Prim '- `(,(Prim 'read '()))) #t]
    [(Prim '+ `(,e1 ,e2)) (and (inert? e1) (inert? e2))]
    [(Let var rhs body) (and (residual? rhs) (residual? body))]
    [else #f]))

(define (pe-residual e)
  (match e
    [(Prim '+ `(,e1 ,(Int n))) (Prim '+ `(,(Int n) ,(pe-residual e1)))]
    [(Prim '+ `(,(Int n) ,e2)) (Prim '+ `(,(Int n) ,(pe-residual e2)))]
    [(Int _) e]
    [(Let var rhs body) (Let var (pe-residual rhs) (pe-residual body))]
    [else (if (inert? e)
              e
              (begin (printf "Cannot be made residual!\n") e))]))

(define (pe-neg-r r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [(Prim '- exp) (pe-neg-r exp)]
    [else (Prim '- (list r))]))

(define (pe-add-r r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [((Int n1) (Prim '+ (list (Int n2) exp)))  (pe-add-r (Int (fx+ n1 n2)) exp)]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp-r e)
  (match e
    [(Int n) e]
    [(Var n) e]
    [(Prim 'read '()) e]
    [(Prim '- (list e1)) (pe-neg-r (pe-exp-r e1))]
    [(Prim '+ (list e1 e2)) (pe-add-r (pe-exp-r e1) (pe-exp-r e2))]
    [(Let x e body) (Let x (pe-exp-r e) (pe-exp-r body))]))

(define (pe-Lvar-r p)
  (match p
    [(Program info e) (Program info (pe-exp (pe-residual e)))]))    


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; shrink pass
(define (shrink-exp e)
  (match e
    ;; atoms to be directly returned
    [(Void) (Void)]
    [(Int i) (Int i)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Var v) (Var v)]
    [(Bool b) (Bool b)]

    ;; complex statements whose sub parts can be shrunk
    [(HasType e t)  (HasType (shrink-exp e) t)]
    [(Let v e b) (Let v (shrink-exp e) (shrink-exp b))]
    [(If cond true-part false-part) (If (shrink-exp cond) (shrink-exp true-part) (shrink-exp false-part))]
    [(Prim '- (list exp)) (Prim '- (list (shrink-exp exp)))]
    [(Prim '+ (list exp1 exp2)) (Prim '+ (list (shrink-exp exp1) (shrink-exp exp2)))]
    [(Prim 'not (list e)) (Prim 'not (list (shrink-exp e)))]
    [(Prim 'eq? (list exp1 exp2)) (Prim 'eq? (list (shrink-exp exp1) (shrink-exp exp2)))]
    [(Prim '< (list exp1 exp2)) (Prim '< (list (shrink-exp exp1) (shrink-exp exp2)))]
    [(Prim 'vector-length (list v)) (Prim 'vector-length (list (shrink-exp v)))]
    [(Prim 'vector ops) (Prim 'vector (map shrink-exp ops))]
    [(Prim 'vector-ref (list exp (Int i))) (Prim 'vector-ref (list (shrink-exp exp) (Int i)))]
    [(Prim 'vector-set! (list exp1 (Int i) exp2)) (Prim 'vector-set! (list (shrink-exp exp1) (Int i) (shrink-exp exp2)))]
    [(Begin exps exp) (Begin (map shrink-exp exps) (shrink-exp exp))]
    [(WhileLoop exp1 exp2) (WhileLoop (shrink-exp exp1) (shrink-exp exp2))]
    [(SetBang exp1 exp2) (SetBang exp1 (shrink-exp exp2))]
    [(Apply fun args) (Apply (shrink-exp fun) (map shrink-exp args))]
    
    ;; the actual shrinking: replacing their ops with ones familiar to us
    [(Prim '- (list arg1 arg2))
     (Prim '+ (list (shrink-exp arg1) (Prim '- (list (shrink-exp arg2)))))] ;; to remove this and add (- e1 e2) everywhere so that we can use subq?     
    [(Prim 'and (list exp1 exp2))
     (If (shrink-exp exp1) (shrink-exp exp2) (Bool #f))]
    [(Prim 'or (list exp1 exp2))
     (If (shrink-exp exp1) (Bool #t) (shrink-exp exp2))]
    [(Prim '>= (list exp1 exp2))
     (Prim 'not (list (Prim '< (list (shrink-exp exp1) (shrink-exp exp2)))))]
    [(Prim '> (list exp1 exp2))
     (let ([tmp-var (gensym 'tmp)])
       (shrink-exp
        (Let tmp-var exp1
             (shrink-exp (Prim '< (list exp2 (Var tmp-var)))))))]
    [(Prim '<= (list exp1 exp2))
     (shrink-exp (Prim 'not (list (shrink-exp (Prim '> (list exp1 exp2))))))]))

(define (shrink p)
  (match p
    [(ProgramDefsExp info defs e) (ProgramDefs info
                                               (append
                                                (for/list ([func defs]) (match func[(Def name parameters return_type info body)(Def name parameters return_type info (shrink-exp body))]))
                                                (list (Def 'main '() 'Integer '() (shrink-exp e)))))]))

;; uniquify
;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(ProgramDefs info defs)
     (define tl
       (for/hash ([d defs])
         (cond 
           [(eq? (Def-name d) 'main) (values 'main 'main)]
           [else (values (Def-name d) (gensym (Def-name d)))])))
     (ProgramDefs
      info
      (for/list ([d defs])
        (match d
          [(Def name params r info bdy)
           (define env
             (for/fold ([env tl])
                       ([(x t) (in-dict params)])
               (dict-set env x (gensym x))))
           (Def (dict-ref tl name)
                (for/list ([(x t) (in-dict params)])
                  (cons (dict-ref env x) t))
                r
                info
                ((uniquify-exp env) bdy))])))]))


(define ((uniquify-exp env) e)
  (define (set-x x new-x) (dict-set env x new-x))
  (match e
    [(Apply f a)
     (Apply ((uniquify-exp env) f) (map (uniquify-exp env) a))]
    [(or (Bool _) (Int _) (Void)) e]
    [(Var x) (Var (dict-ref env x))]
    [(Prim o exp)
     (Prim o (map (uniquify-exp env) exp))]
    [(If a b c)
     (If ((uniquify-exp env) a) ((uniquify-exp env) b) ((uniquify-exp env) c))]
    [(SetBang x e)
     (SetBang (dict-ref env x) ((uniquify-exp env) e))]
    [(Let x e bdy)
     (let ([new-v (gensym x)]) (Let new-v ((uniquify-exp env) e) ((uniquify-exp (set-x x new-v)) bdy)))]
    [(Begin exp fine)
     (Begin (map (uniquify-exp env) exp) ((uniquify-exp env) fine))]
    [(WhileLoop c b) (WhileLoop ((uniquify-exp env) c) ((uniquify-exp env) b))]
    [(HasType e type) (HasType ((uniquify-exp env) e) type)]
    ))

;; Reveal Functions


;(define (reveal-functions p)
;  (match p
;    [(ProgramDefs info defs)
;     (begin
;     (define defs-name-arity
;       (for/hash ([def defs])
;         (values (Def-name def) (length (Def-param* def)))))
;     (set! defs-name-arity (hash-remove defs-name-arity 'main))
;     (ProgramDefs
;      info
;      (for/list ([def defs])
;        (match def
;          [(Def name param* rty info body)
;           (Def name param* rty info
;                ((reveal_function_exp defs-name-arity) body))])) ))]))


(define (reveal-functions p)
  (match p
    [(ProgramDefs info defs)
     (begin
       (define def-to-arity-mapping
         (for/hash ([def defs])
           (if (string=? (symbol->string (Def-name def)) (symbol->string 'main))
               (values '() '())
               (values (Def-name def) (length (Def-param* def))))
           ))
       (ProgramDefs
        info
        (for/list ([def defs])
          (match def
            [(Def name param* rty info body)(Def name param* rty info ((reveal_function_exp def-to-arity-mapping) body))])) ))]))

(define ((reveal_function_exp def-to-arity-mapping) e)
  (define recur (reveal_function_exp def-to-arity-mapping))
  (match e
    [(Void) (Void)]
    [(Int n) (Int n)]
    [(Bool n) (Bool n)]
    [(GetBang e) (GetBang e)]
    [(Var x) (if (hash-ref def-to-arity-mapping x #f) (FunRef x (hash-ref def-to-arity-mapping x)) (Var x))]
    [(Let x e body) (Let x (recur e) (recur body))]
    [(Prim op es) (Prim op (map recur es))]
    [(If e1 e2 e3) (If (recur e1) (recur e2) (recur e3))]
    [(SetBang x e) (SetBang x (recur e))]
    [(Begin es e) (Begin (map recur es) (recur e))]
    [(WhileLoop cnd body) (WhileLoop (recur cnd) (recur body))]
    [(HasType e type) (HasType (recur e) type)]
    [(Apply fun args)(Apply (recur fun) (map recur args))]))




;;limit functions

(define N (vector-length arg-registers))

(define ((limit-exp tup mapping) exp)
  (define limit-exp-util (limit-exp tup mapping))
  (match exp
    [(Int _) exp]
    [(Bool _) exp]
    [(Void) exp]
    [(FunRef _ _) exp]
    [(or (Var x) (GetBang x))
     (if (hash-ref mapping x #f)
         (Prim 'vector-ref (list (Var tup) (Int (hash-ref mapping x #f))))
         exp)]
    [(SetBang x rhs)
     (if (hash-ref mapping x #f)
         (Prim 'vector-set! (list (Var tup) (Int (hash-ref mapping x #f)) (limit-exp-util rhs)))
         (SetBang x (limit-exp-util rhs)))]
    [(If cond true-part false-part) (If (limit-exp-util cond) (limit-exp-util true-part) (limit-exp-util false-part))]
    [(Prim op es) (Prim op (map limit-exp-util es))]
    [(Begin es e) (Begin (map limit-exp-util es) (limit-exp-util e))]
    [(WhileLoop cnd body) (WhileLoop (limit-exp-util cnd) (limit-exp-util body))]
    [(Let x e body) (Let x (limit-exp-util e) (limit-exp-util body))]
    [(HasType e type) (HasType (limit-exp-util e) type)]
    [(Apply fun args)
     (if (> (length args) N)
         (Apply (limit-exp-util fun)
                (let ([args (map limit-exp-util args)])
                  (append (take args (- N 1))
                          (list (Prim 'vector (drop args (- N 1)))))))
         (Apply (limit-exp-util fun) (map limit-exp-util args)))]))

(define (limit-def def)
  (match def
    [(Def name param* rty info body)
     (let* ([tup (gensym 'tup)]
            [mapping
             (if (> (length (Def-param* def)) N)
                 (for/hash ([(x t) (in-dict (drop param* (- N 1)))]
                            [i (in-naturals)])
                   (values x i))
                 (hash))]
            [new-param*
             (if (> (length (Def-param* def)) N)
                 (match param*
                   [`([,xs : ,ts] ...) (append (take param* (- N 1)) `([,tup : (Vector ,@(drop ts (- N 1)))]))])
                 param*)])
       (Def name new-param* rty info ((limit-exp tup  mapping) body)))]))

(define (limit-functions p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (map limit-def defs))]))

;;uncover-get
(define (collect-set! e)
  (match e
    [(Void) (set)]
    [(Var x) (set)]
    [(Int n) (set)]
    [(Prim 'read '()) (set)]
    [(Bool b) (set)]
    [(Collect _) (set)]
    [(Allocate _ _) (set)]
    [(GlobalValue _) (set)]
    [(FunRef _ _) (set)]
    [(Let x rhs body) (set-union (collect-set! rhs) (collect-set! body))]
    [(SetBang var rhs) (set-union (set var) (collect-set! rhs))]
    [(Prim op ops) #:when (member op '(- + not < vector vector-length eq? vector-ref vector-set! vector-length))
                   (apply set-union (map collect-set! ops))]
    [(If cond true-part false-part) (set-union (collect-set! cond) (collect-set! true-part) (collect-set! false-part))]
    [(Begin exps exp) (apply set-union (collect-set! exp) (map collect-set! exps))]
    [(WhileLoop exp1 exp2) (set-union (collect-set! exp1) (collect-set! exp2))]
    [(Prim op '()) (set)]
    [(HasType e type) (collect-set! e)]
    [(Apply f a) (apply set-union (map collect-set! (append (list f) a)))]))

(define ((uncover-get!-exp set!-vars) e)
  (define uncover-get!-exp-util (uncover-get!-exp set!-vars))
  (match e
    [(Var x) (if (set-member? set!-vars x) (GetBang x) (Var x))]
    [(Void) (Void)]
    [(Int n) (Int n)]
    [(Prim 'read '()) e]
    [(Bool b) e]
    [(Collect _) e]
    [(Allocate _ _) e]
    [(GlobalValue _) e]
    [(FunRef _ _) e]
    [(Let x rhs body) (Let x (uncover-get!-exp-util rhs) (uncover-get!-exp-util body))]
    [(SetBang x e) (SetBang x (uncover-get!-exp-util e))]
    [(Prim op ops) #:when (member op '(- + not < vector vector-length eq? vector-ref vector-set! vector-length))
                   (Prim op (map uncover-get!-exp-util ops))]
    [(If cond true-part false-part) (If (uncover-get!-exp-util cond) (uncover-get!-exp-util true-part) (uncover-get!-exp-util false-part))]
    [(Begin exps exp) (Begin (map uncover-get!-exp-util exps) (uncover-get!-exp-util exp))]
    [(WhileLoop cnd body) (WhileLoop (uncover-get!-exp-util cnd) (uncover-get!-exp-util body))]
    [(Apply f a) (Apply (uncover-get!-exp-util f) (map uncover-get!-exp-util a))]
    ))

(define (uncover-get! p)
  (match p
    [(ProgramDefs info defs)
     (ProgramDefs info (for/list ([f_name defs])
                         (match f_name
                           [(Def name param* rty info body)
                            (Def name param* rty info ((uncover-get!-exp (collect-set! body)) body))])))]))

;;expose allocation
(define (expose-allocation-exp p)
  (match p
    [(Void) (Void)]
    [(Int i) (Int i)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Var v) (Var v)]
    [(Bool b) (Bool b)]
    [(FunRef _ _) p]
    [(GetBang _) p]
    [(HasType (Prim 'vector exps) type)
     (let* ([var (gensym 'v)]
            [exps (map expose-allocation-exp exps)]
            [collect-part
             (list
              (let ([numbytes (+ (* 8 (length exps)) 8)])
                (If (Prim '< (list (Prim '+ (list (GlobalValue 'free_ptr) (Int numbytes)))
                                   (GlobalValue 'fromspace_end)))
                    (Void)
                    (Collect (Int numbytes)))))]
            [elements (map (lambda (exp ind) (Prim 'vector-set! (list (Var var) (Int ind) exp)))
                           exps (range 0 (length exps)))])
       (Begin collect-part (Let var (Allocate (length exps) type) (Begin elements (Var var)))))]
    [(Let v e b) (Let v (expose-allocation-exp e) (expose-allocation-exp b))]
    [(If cond true-part false-part) (If (expose-allocation-exp cond) (expose-allocation-exp true-part) (expose-allocation-exp false-part))]
    [(Prim op es) (Prim op (map expose-allocation-exp es))]
    [(SetBang x rhs) (SetBang x (expose-allocation-exp rhs))] 
    [(Begin es body) (Begin (map expose-allocation-exp es) (expose-allocation-exp body))] 
    [(WhileLoop cnd body) (WhileLoop (expose-allocation-exp cnd) (expose-allocation-exp body))]
    [(Apply f a) (Apply (expose-allocation-exp f) (map expose-allocation-exp a))]
    ))

(define (expose-allocation p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (for/list ([f_name defs])
                                                 (match f_name
                                                   [(Def name parameters return_type info body)
                                                    (Def name parameters return_type info (expose-allocation-exp body))])))]))

;;; Removing complex expressions
(define (final_output list_ op)
  (if (empty? list_)
      op
      (let ([var (car (car list_))] [exp (car (cdr (car list_)))])
        (Let var exp (final_output (cdr list_) op)))
      )
  )

(define (return-cdr e)
  (cond
    [(empty? e) empty]
    [else
     (append (cdr (car e)) (return-cdr (cdr e)))]
    ))

(define (rco-atom e)
  (match e
    [(Var x) (list (Var x) (list))]
    [(Int n) (list (Int n) (list))]
    [(Bool b) (list (Bool b) (list))]
    [(Void) (list (Void) (list))]
    [(GlobalValue var)
     (let ([tmp (gensym 'tmp)])
       (append (list tmp) (list (list tmp (GlobalValue var)))))]
    [(Prim op arg)
     (let* (
            [atomicexp_expmapping (map rco-atom arg)]
            [atomicexp (map (compose (lambda (x)
                                       (if (symbol? x)
                                           (Var x)
                                           x))
                                     car) atomicexp_expmapping)]
            [expmapping_intermediate (return-cdr atomicexp_expmapping)]
            [expmapping (filter-not empty? expmapping_intermediate)]
            [tmp (gensym "temp")])
       (append (list tmp) (append (map (lambda (x) x) expmapping) (list (list tmp (Prim op atomicexp))) ))
       )]
    [(Let x v b)
     (let* ([v (rco-exp v)]
            [b (rco-exp b)]
            )
       (cond
         [(is_atom b) (list b  (list x v))]
         [else 
          (let ([tmp (gensym 'tmp)])
            (append (list tmp) (list (list tmp (Let x (rco-exp v) (rco-exp b))))))
          ]))]
    [(If cond true-part false-part)
     (let ([tmp (gensym 'tmp)])
       (append (list tmp) (list (list tmp (If (rco-exp cond) (rco-exp true-part) (rco-exp false-part))))))]
    [(SetBang var exp)
     (let ([tmp (gensym 'tmp)])
       (append (list tmp) (list (list tmp (SetBang var (rco-exp exp))))))]
    [(Begin es body) (let ([tmp (gensym 'tmp)])
                       (append (list tmp) (list (list tmp (Begin (map rco-exp es) (rco-exp body))))))]
    [(WhileLoop exp1 exp2)
     (let ([tmp (gensym 'tmp)])
       (append (list tmp) (list (list tmp (WhileLoop (rco-exp exp1) (rco-exp exp2))))))]
    [(Allocate bytes t)
     (let ([tmp (gensym 'tmp)])
       (append (list tmp) (list (list tmp (Allocate bytes t)))))]
    [(GlobalValue var)
     (let ([tmp (gensym 'tmp)])
       (append (list tmp) (list (list tmp (GlobalValue var)))))]
    [(Collect bytes)
     (let ([tmp (gensym 'tmp)])
       (append (list tmp) (list (list tmp (Collect bytes)))))]
    [(GetBang x)
     (let ([tmp (gensym 'tmp)])
       (append (list tmp) (list (list tmp (Var x)))))]
    [(Apply fun arg)
     (let* ([tmp (gensym 'tmp)]
            [fun-atm-env (rco-atom fun)]
            [fun-atm (car fun-atm-env)]
            [fun-atm (if (symbol? fun-atm)
                         (Var fun-atm)
                         fun-atm)]
            [fun-env-intermediate (cdr fun-atm-env)]
            [fun-env (filter-not empty? fun-env-intermediate)]
            [atomicexp_expmapping (map rco-atom arg)]
            [atomicexp (map (compose (lambda (x)
                                       (if (symbol? x)
                                           (Var x)
                                           x))
                                     car) atomicexp_expmapping)]
            [expmapping_intermediate (return-cdr atomicexp_expmapping)]
            [expmapping (filter-not empty? expmapping_intermediate)])
       (append (list tmp) (append (map (lambda (x) x) (append fun-env expmapping)) (list (list tmp (Apply fun-atm atomicexp))) ))
       )]
    [(FunRef name args)
     (let ([tmp (gensym 'func)])
       (append (list tmp) (list (list tmp (FunRef name args)))))]
    )
  )

(define (rco-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)] 
    [(Bool b) (Bool b)]
    [(Void) (Void)]
    [(GlobalValue var) (GlobalValue var)]
    [(Prim op arg)
     (let* ([atomicexp_expmapping (map rco-atom arg)]
            [atomicexp (map (compose (lambda (x)
                                       (if (symbol? x)
                                           (Var x)
                                           x))
                                     car) atomicexp_expmapping)]
            [expmapping_intermediate (return-cdr atomicexp_expmapping)]
            [expmapping (filter-not empty? expmapping_intermediate)]
            )

       (final_output expmapping (Prim op atomicexp))
       )
     ]
    [(Let var exp body)
     (Let var (rco-exp exp) (rco-exp body))]
    [(If cond true-part false-part) (If (rco-exp cond) (rco-exp true-part) (rco-exp false-part))]
    [(GetBang var) (Var var)]
    [(SetBang var exp) (SetBang var (rco-exp exp))]
    [(Begin es body) (Begin (map rco-exp es) (rco-exp body))]
    [(WhileLoop exp1 exp2) (WhileLoop (rco-exp exp1) (rco-exp exp2))]
    [(Allocate int type) (Allocate int type)]
    [(GlobalValue int) (GlobalValue int)]
    [(Collect int) (Collect int)]
    [(FunRef f args) (FunRef f args)]
    [(Apply fun arg)
     (let* ([tmp (gensym 'tmp)]
            [fun-atm-env (rco-atom fun)]
            [fun-atm (car fun-atm-env)]
            [fun-atm (if (symbol? fun-atm)
                         (Var fun-atm)
                         fun-atm)]
            [fun-env-intermediate (cdr fun-atm-env)]
            [fun-env (filter-not empty? fun-env-intermediate)]
            [atomicexp_expmapping (map rco-atom arg)]
            [atomicexp (map (compose (lambda (x)
                                       (if (symbol? x)
                                           (Var x)
                                           x))
                                     car) atomicexp_expmapping)]
            [expmapping_intermediate (return-cdr atomicexp_expmapping)]
            [expmapping (filter-not empty? expmapping_intermediate)])
       (final_output (append fun-env expmapping) (Apply fun-atm atomicexp))
       )]
    ))


  
(define (is_atom x)
  (or (Int? x)
      (Var? x)
      (Bool? x)))

(define (remove-complex-opera* p)
  (match p
    [(ProgramDefs info def*)
     (ProgramDefs info (map (lambda (d) (struct-copy Def d [body (rco-exp (Def-body d))])) def*))]))


;; explicate-control : R1 -> C0
(define basic-blocks (make-hash))

(define (assign-label blck)
  (match blck
    [(Goto label) (Goto label)]
    [else (let* ([label (gensym 'label)] [_ (dict-set! basic-blocks label blck)] [lab (Goto label)]) lab)]))

(define (assign-block-to-label blck label_sym)
  (begin
    (dict-set! basic-blocks label_sym blck)
    (Goto label_sym)))

(define (create_block tail)
  (match tail
    [(Goto label) (Goto label)]
    [else
     (let ([label (gensym 'block)])
       (dict-set! basic-blocks label tail)
       (Goto label))]
    ))

(define (explicate_pred cnd thn els)
  (match cnd
    [(Var x) (IfStmt (Prim 'eq? (list (Bool #t) (Var x)))
                     (create_block thn)
                     (create_block els))]
    [(Let x rhs body) (explicate_assign rhs x (explicate_pred body thn els))]
    [(Bool #t) (create_block thn)]
    [(Bool #f) (create_block els)]
    [(Prim op es) #:when (or (eq? op 'eq?) (eq? op '<))
                  (IfStmt (Prim op es)
                          (create_block thn)
                          (create_block els))]
    [(Prim 'not (list e1))
     (explicate_pred e1 els thn)]
    [(If cond true-part else-part)
     (explicate_pred cond
                     (explicate_pred true-part thn els)
                     (explicate_pred else-part thn els))]
    [(Begin es body) (explicate-effect (Begin es (Void)) (explicate_pred body thn els))]
    [(Apply fun-name es)
     (define tmp (gensym 'tmp))
     (Seq (Assign (Var tmp) (Call fun-name es))
          (IfStmt (Prim 'eq? (list (Var tmp) (Bool #t)))
                  (create_block thn)
                  (create_block els)))]
    [else (error "explicate_pred error: " cnd)]))

(define (explicate-small? e)
  (match e
    [(Var x) #t] 
    [(Int n) #t] 
    [(Bool b) #t] 
    [(Void) #t]
    [(Allocate _ _) #t] 
    [(GlobalValue var) #t]
    [else #f]
    )
  )

(define (explicate-effect e cont)
  (match e
    [_ #:when (explicate-small? e) cont]
    [(Prim 'read '()) (Seq (Prim 'read '()) cont)]
    [(Prim 'vector-set! es) (Seq (Prim 'vector-set! es) cont)]
    [(Prim op es) cont] 
    [(Let x rhs body) (explicate_assign rhs x (explicate-effect body cont))] 
    [(If cnd thn els) 
     (let [(cont-block (create_block cont))] 
       (explicate_pred cnd
                       (explicate-effect thn cont-block)
                       (explicate-effect els cont-block)))] 
    [(SetBang x rhs) (explicate_assign rhs x cont)] 
    [(Begin es body) (foldr explicate-effect cont (append es (list body)))]
    [(WhileLoop cnd body) (let ([label (gensym 'loop)])
                            (begin
                              (dict-set! basic-blocks label (explicate_pred cnd (explicate-effect body (Goto label)) cont))
                              (Goto label)))]
    [(Collect bytes) (Seq (Collect bytes) cont)]
    [(FunRef x n) cont]
    [(Apply fun-name es) cont]
    [else (error "explicate-effect unhandled case" e)]))

(define (explicate_tail e)
  (match e
    [_ #:when (explicate-small? e) (Return e)]
    [(Let x rhs body) (explicate_assign rhs x (explicate_tail body))]
    [(Prim op es) (Return e)]
    [(Begin es body) (foldr explicate-effect (explicate_tail body) es)]
    [(If cond true-part false-part)
     (explicate_pred
      cond
      (create_block (explicate_tail true-part))
      (create_block (explicate_tail false-part))
      )]
    [(FunRef x n) (Return (FunRef x n))]
    [(Apply fun-name es) (TailCall fun-name es)]
    [else (error "explicate_tail unhandled case" e)]))

(define (explicate_assign e x cont)
  (match e
    [_ #:when (explicate-small? e) (Seq (Assign (Var x) e) cont)]
    [(Let y rhs body) (explicate_assign rhs y (explicate_assign body x cont))]
    [(Prim op es) (Seq (Assign (Var x) e) cont)]
    [(Begin es body)
     (let* ([tail (explicate_assign body x cont)] [seq (foldr explicate-effect tail es)]) seq)]
    [(WhileLoop cnd body) (let ([label (gensym 'loop)])
                            (begin
                              (dict-set! basic-blocks label (explicate_pred cnd (explicate-effect body (Goto label)) cont))
                              (Seq (Assign (Var x) (Void)) (Goto label))))]
    [(SetBang y rhs) (Seq (Assign (Var x) (Void)) (explicate_assign rhs y cont))]
    [(If cond true-part false-part)
     (explicate_pred
      cond
      (explicate_assign true-part x cont)
      (explicate_assign false-part x cont)
      )]
    [(Collect bytes) (Seq (Collect bytes) cont)]
    [(FunRef fun n) (Seq (Assign (Var x) (FunRef fun n)) cont)]
    [(Apply fun-name es) (Seq (Assign (Var x) (Call fun-name es)) cont)]
    [else (error "explicate_assign unhandled case" e)]))

(define (explicate-control-def d)
  (match d
    [(Def func-name args ret-type info exp)
     (begin
       (set! basic-blocks (make-hash))
       (dict-set! basic-blocks (symbol-append func-name 'start) (explicate_tail exp))
       (Def func-name args ret-type info (hash->list basic-blocks))
       )]))

(define (explicate-control p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (for/list ([d defs]) (explicate-control-def d)))]))

;;; select-instructions : C0 -> pseudo-x86
(define (select-instruction-atm e)
  (match e
    [(Var v) (Var v)]
    [(Int n) (Imm n)]
    [(Bool #t) (Imm 1)]
    [(Bool #f) (Imm 0)] 
    [(Void) (Imm 0)]
    [(GlobalValue g) (Global g)]
    [else (error "si-atm unhandled case" e)]))

;; here making the second arg of cmpq as non immediate, but for cmpq first needs to be
(define (handle-cmp-stmnt e flag)
  (match e
    [(Assign (Var v) (Prim op `(,atm1 ,atm2)))
     `(,(Instr 'cmpq `(,(select-instruction-atm atm2) ,(select-instruction-atm atm1)))
       ,(Instr 'set (list flag (ByteReg 'al)))
       ,(Instr 'movzbq `(,(ByteReg 'al) ,(Var v))))
     ])
  )

(define (masking-function t [mask 0])
  (match t
    [`(Vector) mask]
    [`(Vector (Vector . ,_)) (bitwise-ior mask 1)]
    [`(Vector ,_) mask]
    [`(Vector . ((Vector . ,_) . ,rest)) (masking-function `(Vector . ,rest) (arithmetic-shift (bitwise-ior mask 1) 1))]
    [`(Vector . (,t . ,rest)) (masking-function `(Vector . ,rest) (arithmetic-shift mask 1))]
    [else (error "Unable to mask" t)]))


(define (select-instruction-stmnt e)
  (match e
    [(Assign (Var v) (Int i)) `(,(Instr 'movq `(,(Imm i) ,(Var v))))]
    [(Assign (Var v) (Bool b)) `(,(Instr 'movq `(,(select-instruction-atm (Bool b)) ,(Var v))))]
    [(Assign (Var v) (Var u)) `(,(Instr 'movq `(,(Var u) ,(Var v))))]
    [(Assign (Var v) (Void)) `(,(Instr 'movq `(,(Imm 0) ,(Var v))))]
    [(Assign (Var v) (GlobalValue g)) `(,(Instr 'movq `(,(Global g) ,(Var v))))]
    [(Prim 'read '()) `( ,(Callq `read_int 0))]
    [(Assign (Var v) (Prim 'read '()))
     `( ,(Callq `read_int 0)
        ,(Instr 'movq `(,(Reg 'rax) ,(Var v))))
     ]
    ;; - operator
    [(Assign (Var v) (Prim '- `(,var1)))
     `( ,(Instr 'movq `(,(select-instruction-atm var1) ,(Var v)))
        ,(Instr 'negq `(,(Var v))))
     ]
    ;; + operator
    [(Assign (Var v) (Prim '+ `(,var1 ,var2)))
     (let ([var1 (select-instruction-atm var1)]
           [var2 (select-instruction-atm var2)])
       (cond
         [(equal? (Var v) var1)
          `( ,(Instr 'addq `(,(select-instruction-atm var2) ,(Var v))))
          ]
         [(equal? (Var v) var2)
          `( ,(Instr 'addq `(,(select-instruction-atm var1) ,(Var v))))
          ]
         [else
          `( ,(Instr 'movq `(,var1 ,(Var v)))
             ,(Instr 'addq `(,var2 ,(Var v))))
          ]
         ))]
    ;; not operator
    [(Assign (Var v) (Prim 'not `(,arg)))
     (match arg
       [(Var v) `(,(Instr 'xorq `(,(Imm 1) ,(Var v))))]
       [else `(,(Instr 'movq `(,(select-instruction-atm arg) ,(Var v)))
               ,(Instr 'xorq `(,(Imm 1) ,(Var v))))]
       )
     ]
    ;; eq? operator
    [(Assign (Var v) (Prim 'eq? `(,atm1 ,atm2))) (handle-cmp-stmnt e 'e)]
    [(Assign (Var v) (Prim '< `(,atm1 ,atm2))) (handle-cmp-stmnt e 'l)]

    [(Assign (Var v) (Prim 'vector-set! `(,tup ,(Int n), rhs)))
     `(,(Instr 'movq `(,tup ,(Reg 'r11))) ,(Instr 'movq `(,(select-instruction-atm rhs) ,(Deref 'r11 (*(8 (+ n 1)))))),(Instr 'movq `(,(Imm 0) ,(Var v))))]
    [(Assign (Var v) (Collect bytes))
     `(,(Instr 'movq `(,(Reg 'r15) ,(Reg 'rdi))) ,(Instr 'movq `(,(Imm bytes) ,(Reg 'rsi))),(Callq 'collect 2))]
    [(Assign (Var v) (Allocate len t))
     `(,(Instr 'movq `(,(Global 'free_ptr) ,(Reg 'r11))) ,(Instr 'addq `(,(Imm (* 8 (+ len 1))) ,(Global 'free_ptr))),(Instr 'movq `(,(Imm (bitwise-ior 1 (arithmetic-shift len 1) (arithmetic-shift (masking-function t) 7))) ,(Deref 'r11 0))),(Instr 'movq `(,(Reg 'r11) ,(Var v))))]
    [(Collect (Int n))
     `(,(Instr 'movq (list (Reg 'r15) (Reg 'rdi))) ,(Instr 'movq (list (Imm n) (Reg 'rsi))) ,(Callq 'collect 2))]
    [(Prim 'vector-set! (list vec (Int pos) rhs)) ;; vector ref can be a statement
     `(,(Instr 'movq (list vec (Reg 'r11))) ,(Instr 'movq (list (select-instruction-atm rhs) (Deref 'r11 (* (+ 1 pos) 8)))))]
    ;    [(Assign x (Prim 'vector-ref (list vec (Int pos) rhs)))
    ;     `(,(Instr 'movq (list (select-instruction-atm rhs) (Deref 'r11 (* (+ 1 pos) 8)))) `(,(Instr 'movq (list vec (Reg 'r11))) ,(Instr 'movq (list (Deref 'r11 (* (+ 1 pos) 8)) x))))]
    [(Assign x (Prim 'vector-length (list vec)))
     `(,(Instr 'movq (list vec (Reg 'r11))) ,(Instr 'movq (list (Deref 'r11 0) x)) ,(Instr 'sarq (list (Imm 1) x)) ,(Instr 'andq (list (Imm 127) x)))]
    [(Assign x (Prim 'vector-ref (list vec (Int pos))))
     `(,(Instr 'movq (list vec (Reg 'r11))) ,(Instr 'movq (list (Deref 'r11 (* (+ 1 pos) 8)) x)))]
    [(Assign x (Prim 'vector-set! (list vec (Int pos) rhs)))
     `(,(Instr 'movq (list vec (Reg 'r11))) ,(Instr 'movq (list (select-instruction-atm rhs) (Deref 'r11 (* (+ 1 pos) 8)))) ,(Instr 'movq (list (Var x) (Imm 0))))]
    [(Assign (Var x) (Call f args))
     (append (for/list ([arg (map select-instruction-atm args)] [r arg-registers])
               (Instr 'movq (list arg (Reg r))))
             (list (IndirectCallq f (length args))
                   (Instr 'movq (list (Reg 'rax) (Var x)))))]
    [(Call f args)
     (append (for/list ([arg (map select-instruction-atm args)] [r arg-registers])
               (Instr 'movq (list arg (Reg r))))
             (list (IndirectCallq f (length args))))]
    [(Assign (Var x) (FunRef name args)) `(,(Instr 'leaq (list (Global name) (Var x))))]
    [else (error "si-stmt unhandled case" e)]))


;; same as above handle
(define (handle-cmp-tail e flag)
  (match e
    [(IfStmt (Prim op `(,a1 ,a2)) (Goto l1) (Goto l2))
     `(,(Instr 'cmpq `(,(select-instruction-atm a2) ,(select-instruction-atm a1)))
       ,(JmpIf flag l1)
       ,(Jmp l2))
     ])
  )

(define (select-instruction-tail e lbl)
  (match e
    [(Return (Var v))
     `( ,(Instr 'movq `(,(Var v) ,(Reg 'rax)))
        ,(Jmp (symbol-append lbl 'conclusion)))
     ]
    [(Return (Int i))
     `( ,(Instr 'movq `(,(Imm i) ,(Reg 'rax)))
        ,(Jmp (symbol-append lbl 'conclusion)))
     ]
    [(Return (Bool b))
     `(,(Instr 'movq `(,(select-instruction-atm (Bool b)) ,(Reg 'rax)))
       ,(Jmp (symbol-append lbl 'conclusion)))
     ]
    [(Return (Prim 'read '()))
     `( ,(Callq 'read_int 0)
        ,(Jmp (symbol-append lbl 'conclusion)))
     ]
    [(Return (Prim '- `(,var1)))
     `( ,(Instr 'movq `(,(select-instruction-atm var1) ,(Reg 'rax)))
        ,(Instr 'negq `(,(Reg 'rax)))
        ,(Jmp (symbol-append lbl 'conclusion)))
     ]
    [(Return (Prim '+ `(,var1 ,var2)))
     `( ,(Instr 'movq `(,(select-instruction-atm var1) ,(Reg 'rax)))
        ,(Instr 'addq `(,(select-instruction-atm var2) ,(Reg 'rax)))
        ,(Jmp (symbol-append lbl 'conclusion)))
     ]
    [(Return (Prim '< `(,var1 ,var2)))
     `(,(Instr 'cmpq `(,(select-instruction-atm var2) ,(select-instruction-atm var1)))
       ,(Instr 'set (list 'l (ByteReg 'al)))
       ,(Instr 'movzbq `(,(ByteReg 'al) ,(Reg 'rax))))
     ]
    
    [(Return (Prim 'eq `(,var1 ,var2)))
     `(,(Instr 'cmpq `(,(select-instruction-atm var2) ,(select-instruction-atm var1)))
       ,(Instr 'set (list 'e (ByteReg 'al)))
       ,(Instr 'movzbq `(,(ByteReg 'al) ,(Reg 'rax))))
     ]
    [(Seq stmt tail)  (append (select-instruction-stmnt stmt) (select-instruction-tail tail lbl))]
    [(Goto l) `(,(Jmp l))]
    [(IfStmt (Prim 'eq? `(,a1 ,a2)) (Goto l1) (Goto l2)) (handle-cmp-tail e 'e)]
    [(IfStmt (Prim '< `(,a1 ,a2)) (Goto l1) (Goto l2)) (handle-cmp-tail e 'l)]

    [(Return (Prim 'not (list a)))
     (if (equal? a (Reg 'rax))
         (list (Instr 'xorq (list (Imm 1) (Reg 'rax))))
         (list (Instr 'movq (list (select-instruction-atm a) (Reg 'rax)))
               (Instr 'xorq (list (Imm 1) (Reg 'rax)))))]
    
    [(Return (Prim 'vector-ref `(,tup ,(Int n))))
     `(,(Instr 'movq `(,tup ,(Reg 'r11)))
       ,(Instr 'movq `(,(Deref 'r11 (* 8 (+ n 1))) ,(Reg 'rax)))
       ,(Jmp (symbol-append lbl 'conclusion)))]
    [(Return (Prim 'vector-set! `(,tup ,(Int n), rhs)))
     `(,(Instr 'movq `(,tup ,(Reg 'r11)))
       ,(Instr 'movq `(,(select-instruction-atm rhs) ,(Deref 'r11 (*(8 (+ n 1))))))
       ,(Instr 'movq `(,(Imm 0) ,(Reg 'rax)))
       ,(Jmp (symbol-append lbl 'conclusion)))]
    [(Prim 'vector-length (list vec))
     `(,(Instr 'movq (list (select-instruction-atm vec) (Reg 'r11))) 
       ,(Instr 'movq (list (Deref 'r11 0) (Reg 'rax)))
       ,(Instr 'sarq (list (Imm 1) (Reg 'rax)))
       ,(Instr 'andq (list (Imm 63) (Reg 'rax))))]
    
    [(TailCall f args)
     (append (for/list ([arg (map select-instruction-atm args)] [r arg-registers])
               (Instr 'movq (list arg (Reg r))))
             (list (TailJmp f (length args))))]
    [(Return (FunRef name args))
     `(,(Instr 'leaq (list (Global name) (Reg 'rax)))
       ,(Jmp (symbol-append lbl 'conclusion)))]
    
    [else (error "si-tail unhandled case" e)]))

(define (select-instr-def def)
  (match def
    [(Def name `([,xs : ,ts] ...) rty info blocks)
     (define new-blocks
       (for/list ([(label tail) (in-dict blocks)])
         (cons label (Block '() (select-instruction-tail tail name)))))
     (define param-moves
       (for/list ([x xs] [r arg-registers])
         (Instr 'movq (list (Reg r) (Var x)))))
     (define start-label (symbol-append name 'start))
     (define new-start-block
       (match (dict-ref new-blocks start-label)
         [(Block info instrs)
          (Block info (append param-moves instrs))]))
     (define new-info
       (dict-set-all
        info
        `((locals-types . ,(append (map cons xs ts)
                                   (dict-ref info 'locals-types)))
          (num-params . ,(length xs)))))
     (Def name '() rty new-info
          (dict-set new-blocks start-label new-start-block))]))

(define (select-instructions p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (map select-instr-def defs))]))

;; Constant propogation
(define (constant-propogation-instrs instrs env)
  (match instrs
    [(cons first-instr rest)
     (match first-instr
       [(Instr 'cmpq `(,arg1 ,arg2)) (cons (Instr 'cmpq `(,(dict-ref env arg1 arg1) ,arg2)) (constant-propogation-instrs rest env))]
       [(Instr 'movq `(,(Imm n) ,(Var y))) (cons first-instr (constant-propogation-instrs rest (dict-set env (Var y) (Imm n))))]
       [(Instr it `(,arg)) (cons first-instr (constant-propogation-instrs rest (dict-remove env arg)))]
       [(Instr it `(,arg1 ,arg2)) (cons (Instr it (list (dict-ref env arg1 arg1) arg2)) (constant-propogation-instrs rest (dict-remove env arg2)))]
       [(Instr 'movq `(,(Var var1) ,(Var var2)))
        (let ([const (dict-ref env (Var var1) #f)])
          (case
              [(equal? #f const) (cons first-instr (constant-propogation-instrs rest (dict-remove env (Var var2))))]
            [else (cons (Instr 'movq (list const (Var var2))) (constant-propogation-instrs rest (dict-set env (Var var2) const)))]))]
       [else (cons first-instr (constant-propogation-instrs rest env))])]
    [else instrs]))

(define (constant-propogation p)
  (match p
    [(X86Program info e) (X86Program info (constant-propogation-instrs e '()))]))
     
;; assign homes
(define (assign-home-atm var-location atm)
  (match atm
    [(Imm _) atm]
    [(Reg _) atm]
    [(Var v) (let ([p (assv v var-location)]) (Deref 'rbp (cdr p)))]
    [else (error "ah-atm unhandled case" atm)])
  )

(define (assign-home-instruction var-location instr)
  (match instr
    [(Jmp _) instr]
    [(Callq _ _) instr]
    [(Instr op args) (let ([args (map (lambda (l) (assign-home-atm var-location l)) args)]) (Instr op args))]
    [else (error "ah-instr unhandled case" instr)]))

(define (assign-home-block var-location blk)
  (match blk
    [(Block info instrs) (let ([instrs-new (map (lambda (l) (assign-home-instruction var-location l)) instrs)]) (Block info instrs-new))]
    )
  )

(define (extract-variables local-list)
  (let ([locals (assv 'locals-types local-list)])
    (cond
      [(empty? locals) '()]
      [ else  (map (lambda (p) (car p))  (cdr locals))]
      )
    )
  )

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-block blk lh)
  (match blk
    [(Block info is)
     (Block info
            (for/list ([i is])
              (assign-instruction i lh)))]))

(define (assign-instruction i lh)
  (match i
    [(Instr op `(,a))
     (Instr op (list (assign-arg a lh)))]
    [(Instr op `(,src ,dst))
     (Instr op (list (assign-arg src lh)
                     (assign-arg dst lh)))]
    [else i]))

(define (assign-arg a lh)
  (match a
    [(Var x) (dict-ref lh x)]
    [else a]))

;; uncover-live
(define (uncover-live p)
  (match p
    [(ProgramDefs info defs)
     (ProgramDefs info (map uncover-defs defs))]))

(define nbs (make-hash))
(define label->live (make-hash))
(define wl (make-queue))

(define (adj-labels b conc-label)
  (match b
    [(Block inf is)
     (define (check l) (not (equal? l conc-label)))
     (for/fold ([a (set)]) ([i is])
       (match i
         [(JmpIf _ l) (set-add a l)]
         [(Jmp l)
          #:when (check l)
          (set-add a l)]
         [else a]))]))

(define (uncover-defs defs)
  (match defs
    [(Def f eps rty info blks)
     (define G (make-G blks (symbol-append f 'conclusion)))
     (hash-set! label->live (symbol-append f 'conclusion) (set 'rax 'rsp))
     (for ([label (in-dict-keys blks)])
       (hash-set! label->live label (set)))
     (for ([label (tsort (transpose G))])
       (enqueue! wl label))
     (while (not (queue-empty? wl))
            (define l (dequeue! wl))
            (define-values (new-block nlb)
              (uncover-block (dict-ref blks l) label->live))
            (hash-set! nbs l new-block)
            (unless (equal? nlb (hash-ref label->live l))
              (hash-set! label->live l nlb)
              (for ([label-add (in-neighbors (transpose G) l)])
                (enqueue! wl label-add))))
     (Def f eps rty
          (dict-set info 'label->live label->live)
          (for/list ([label (in-dict-keys blks)])
            (cons label (hash-ref nbs label))))]))

(define (make-G blks conc-label)
  (define G (directed-graph '()))
  (define (edge G l) (add-vertex! G l))
  (for ([l (in-dict-keys blks)]) (edge G l))
  (define (dir G s t) (add-directed-edge! G s t))
  (for ([(s b) (in-dict blks)]) (for ([t (adj-labels b conc-label)]) (dir G s t))) G)


(define (uncover-block blk label->live)
  (match blk
    [(Block info is)
     (values
      (Block (dict-set info 'live-afters (cdr (uncover-ins (reverse is) (list (set)) label->live))) is)
      (car (uncover-ins (reverse is) (list (set)) label->live)))]))

(define (uncover-ins ri is label->live)
  (match ri
    ['() is]
    [`(,ins . ,rst)
     (uncover-ins rst (cons (uncover-i ins (car is) label->live) is) label->live)]))

(define (uncover-i i lp label->live)
  (match i
    [(JmpIf _ l) (set-union lp (dict-ref label->live l))]
    [(Jmp l) (dict-ref label->live l)]
    [else (set-union (set-subtract lp (writes i)) (reads i))]))


(define (writes instr)
  (match instr
    [(Instr 'cmpq _) (set)]
    [(Instr op (list a1 a2)) (evfa a1)]
    [(Instr 'negq (list a)) (evfa a)]
    [(Instr 'set (list _ a)) (evfa a)]
    [(Callq label n) (caller-save-for-alloc)]
    [(Jmp _) (set)]
    [(JmpIf _ _) (set)]
    [(Instr 'leaq (list a1 a2)) (evfa a2)]
    [(or (IndirectCallq a ar)
         (TailJmp a ar))
     (caller-save-for-alloc)]))

(define (reads instr)
  (match instr
    [(Callq label n) (set)]
    [(Jmp _) (set)]
    [(JmpIf _ _) (set)]
    [(Instr 'leaq (list a1 a2)) (evfa a1)]
    [(Instr (or 'addq 'subq 'xorq 'cmpq) (list a1 a2))
     (set-union (evfa a1) (evfa a2))]
    [(Instr (or 'movq 'movzbq) (list arg1 arg2))
     (evfa arg1)]
    [(or (Instr 'negq (list a))
         (Instr 'set (list _ a)))
     (evfa a)]
    [(or (IndirectCallq a ar)
         (TailJmp a ar))
     (set-union (evfa a)
                (vector->set (vector-take arg-registers ar)))]))

(define (evfa arg)
  (match arg
    [(ByteReg r) (set (byte-reg->full-reg r))]
    [(Imm n) (set)]
    [(Global _) (set)]
    [(Var x) (set x)]
    [(Deref r o) (set r)]
    [(Reg r) (set r)]
    [(FunRef f ar) (set)]))

;; move-bias graph
(define (move-bias-instruction instr graph)
  (match instr
    [(Instr 'movq (list src dst))
     (begin
       (if (equal? src dst) (void) (add-edge! graph src dst))
       graph)
     ]
    [else graph]
    ))

(define (move-bias-block blk)
  (match blk
    [(Block info instructions)
     (let ([graph (undirected-graph '())])
       (begin
         (for ([instr instructions]) (move-bias-instruction instr graph))
         graph)
       )
     ]))


(define (build-move-bias-graph p)
  (match p
    [(X86Program info e)
     (X86Program (dict-set info 'move-bias-graph (move-bias-block (dict-ref e 'start))) e)]))


; build-interference
(define (build-interference p)
  (match p
    [(ProgramDefs info defs)
     (ProgramDefs info (map build-defs defs))]))

(define (build-defs d)
  (match d
    [(Def f ep rty inf blocks)
     (define i-graph (directed-graph '()))
     (define (add-v v) (add-vertex! i-graph v))
     (define locals-types (dict-ref inf 'locals-types))
     (for ([lt locals-types])
       (add-v (car lt)))
     (define label->live (dict-ref inf 'label->live))
     (for ([(label lives) (in-dict label->live)])
       (for ([li lives])
         (add-v li)))
     (for ([(l blk) (in-dict blocks)])
       (match blk
         [(Block info is)
          (define live-afters (dict-ref info 'live-afters))
          (build-interf is live-afters locals-types i-graph)]))
     (Def f ep rty (dict-set inf 'conflicts i-graph) blocks)]))

(define (root-type? i)
  (match i
    [`(Vector ,T ...) #t]
    [else #f]))

(define (build-interf is las lts interf)
  (define (check-two d) (not (root-type? (dict-ref lts d #f))))
  (define (check-one v d) (not (equal? v d)))
  (define (add-e v d) (add-edge! interf v d))
  (define (check-three v) (root-type? (dict-ref lts v #f)))
  (for ([instr is] [la las])
    (match instr
      [(Instr 'movq (list s d))
       (for ([v la])
         (for ([d (evfa d)]
               #:when (not (or (equal? (Var v) s) (equal? v d))))
           (add-e v d)))]
      [(or (IndirectCallq _ _) (Callq _ _))
       (for ([v la])
         (if (check-three v)            
             (begin
               (for ([d registers-for-alloc])
                 (add-e v d))
               (for ([d la]
                     #:when (check-two d))
                 (add-e v d)))
             (for ([d (caller-save-for-alloc)])
               (add-e v d))))]
      [(Instr 'movzbq (list (ByteReg s) d))
       (for ([v la])
         (for ([d (evfa d)]
               #:when (not (equal? (byte-reg->full-reg s) d)))
           (add-e v d)))]
      [else
       (for ([v la])
         (for ([d (writes instr)]
               #:when (check-one v d))
           (add-e v d)))])))

; allocate

(define (allocate-registers p)
  (match p
    [(ProgramDefs info defs)
     (ProgramDefs info (map allocate-defs defs))]))

(define (allocate-defs d)
  (match d
    [(Def f eps rty info blks)
     (define interf (dict-ref info 'conflicts))
     (define vars
       (for/list ([(var type) (in-dict (dict-ref info 'locals-types))]) var))
     (define-values (old-varsc lc) (colour-G interf vars))
     (define-values (varsc ns nrs)
       (recolour old-varsc (dict-ref info 'locals-types) lc))
     (define locals-homes
       (for/hash ([v vars])
         (define home (colour->home (hash-ref varsc v)
                                    (num-registers-for-alloc)
                                    (set-count (used-callee-regs varsc))
                                    nrs))
         (values v home)))
     (define new-info `((used-callee . (used-callee-regs vars-colours)) (num-spilled . ns) (num-root-spills . ,nrs) (num-params . ,(dict-ref info 'num-params))))
     (Def f eps rty
          new-info
          (for/list ([(l blk) (in-dict blks)])
            (cons l (assign-block blk locals-homes))))]))

(define (colour-G interf vs)
  (define vars-colours (make-hash))
  (define ucols (make-hash))
  (define Q (make-pqueue
             (lambda (u v) (>= (set-count (hash-ref ucols u)) (set-count (hash-ref ucols v))))))
  (define vnodes (make-hash))

  (define lc 0)
  (define (check-set l) (set-member? registers l))
  (for ([v vs])
    (hash-set! ucols v (list->set (map register->color (for/list ([location (in-neighbors interf v)] #:when (check-set location)) location))))
    (hash-set! vnodes v (pqueue-push! Q v)))

  (while (> (pqueue-count Q) 0)
         (define var (pqueue-pop! Q))
         (define colour (for/first ([c (in-naturals)]
                                    #:when (not (set-member? (hash-ref ucols var) c)))
                          c))
         (cond [(> colour lc)
                (set! lc colour)])
         (hash-set! vars-colours var colour)
         (for ([neighbor (in-neighbors interf var)]
               #:when (not (set-member? registers neighbor)))
           (hash-set! ucols
                      neighbor (set-add (hash-ref ucols neighbor) colour))
           (pqueue-decrease-key! Q (hash-ref vnodes neighbor))))

  (values vars-colours lc))

(define (recolour vcols vtypes largest-colour)
  (define ssc (num-registers-for-alloc))
  (when (largest-colour . < . (num-registers-for-alloc))
    (values vcols 0 0))

  (define sc (range (num-registers-for-alloc) (+ largest-colour 1)))
  (define src
    (for/set ([(var colour) (in-dict vcols)]
              #:when (and (colour . >= . (num-registers-for-alloc))
                          (root-type? (dict-ref vtypes var))))
      colour))
  (define snrc
    (for/list ([colour sc]
               #:when (not (set-member? src colour)))
      colour))

  (define mapping
    (for/hash ([c sc]
               [newc (append (set->list src)
                             snrc)])
      (values c newc)))

  (define nvc
    (for/hash ([(var colour) (in-dict vcols)])
      (if (colour . >= . ssc)
          (values var (hash-ref mapping colour))
          (values var colour))))
  (values nvc (length snrc) (set-count src)))

(define (used-callee-regs vc)
  (for/set ([(v c) vc]
            #:when (and (set-member? (callee-save-for-alloc) (color->register c)) (< c (num-registers-for-alloc))))
    (color->register c)))

(define (colour->home c nrfa nuc nrs)
  (cond
    [(< c nrfa)
     (Reg (color->register c))]
    [(< c (+ nrfa nrs))
     (Deref 'r15 (* -8 (+ (- c nrfa) 1)))]
    [(Deref 'rbp (* -8 (+ (+ (- c nrfa nrs) 1) nuc)))]))

;patch
(define (iter-defs ds)
  (for/list ([d ds])
    (match d
      [(Def f eps rty info blks)
       (Def f eps rty info (for/list ([(l blk) (in-dict blks)])
                             (cons l (patch-block blk))))])))
(define (patch-instructions p)
  (match p
    [(ProgramDefs info ds)
     (ProgramDefs
      info
      (iter-defs ds))]))

(define (patch-block block)
  (define (tail a) (not (equal? a (Reg 'rax))))
  (define (regs a b c d) (and (eq? a b) (eq? c d)))
  (define (anti a) (not (Reg? a)))
  (match block

    [(Block info is)
     (Block
      info
      (append-map
       (lambda (i)
         (match i
           [(TailJmp a ar)
            #:when (tail a)
            (list (Instr 'movq (list a (Reg 'rax)))
                  (TailJmp (Reg 'rax) ar))]
           [(Instr 'movq (list (Deref r1 o1) (Deref r2 o2)))
            #:when (regs r1 r2 o1 o2)
            '()]       
           [(Instr 'leaq (list a1 a2))
            #:when (anti a2)
            (list (Instr 'leaq (list a1 (Reg 'rax)))
                  (Instr 'movq (list (Reg 'rax) a2)))]
           [(Instr op (list (Deref r1 o1) (Deref r2 o2)))
            (list (Instr 'movq (list (Deref r1 o1) (Reg 'rax)))
                  (Instr op (list (Reg 'rax) (Deref r2 o2))))]
           [(Instr 'movzbq (list a1 a2))
            #:when (anti a2)
            (list (Instr 'movzbq (list a1 (Reg 'rax)))
                  (Instr 'movq (list (Reg 'rax) a2)))]
           [(Instr 'cmpq (list a1 (Imm n)))
            (list (Instr 'movq (list (Imm n) (Reg 'rax)))
                  (Instr 'cmpq (list a1 (Reg 'rax))))]
           [(Instr 'movq (list (Reg r1) (Reg r2)))
            #:when (eq? r1 r2)
            '()]
           [else (list i)])) is))]))

; prelude
(define (prelude-and-conclusion p)
  (match p
    [(ProgramDefs info defs)
     (define newd (map pc-defs defs))
     (X86Program info (append-map Def-body newd))]))

(define (pc-defs def)
  (match def
    [(Def f eps rty info blocks)
     (define rspd (if (even? (+ (set-count (dict-ref info 'used-callee)) (dict-ref info 'num-spilled)))
                      (* 8 (dict-ref info 'num-spilled))
                      (* 8 (+ 1 (dict-ref info 'num-spilled)))))
     
     (define new-blocks
       (for/list ([(l blk) (in-dict blocks)])
         (cons l
               (expand-jump blk (dict-ref info 'used-callee) rspd (dict-ref info 'num-root-spills)))))
     (Def f eps rty info
          (append 
           new-blocks
           (list (generate-prelude f (dict-ref info 'used-callee) rspd (dict-ref info 'num-root-spills))
                 (cons (symbol-append f 'conclusion)
                       (Block '()
                              (append (conclusion-is (dict-ref info 'used-callee) rspd (dict-ref info 'num-root-spills))
                                      (list (Retq))))))))]))


(define (expand-jump block uc rspd nrs)
  (match block
    [(Block info is)
     (Block
      info
      (append*
       (for/list ([i is])
         (match i
           [(Instr 'leaq (list (FunRef name arity) a2))
            (list (Instr 'leaq (list (Global name) a2)))]
           [(TailJmp arg arity)
            (append (conclusion-is uc rspd nrs)
                    (list (IndirectJmp arg)))]
           [else (list i)]))))]))

(define (generate-prelude f uc rspd nrs)
  (define start (list (Instr 'pushq (list (Reg 'rbp)))
                      (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))))
  (cons f
        (Block
         '()
         (append
          start
          (for/list ([reg uc])
            (Instr 'pushq (list (Reg reg))))
          (if (= rspd 0) '() (list (Instr 'subq (list (Imm rspd) (Reg 'rsp)))))
          (if (eq? f 'main) (list
                             (Instr 'movq (list (Imm 16384) (Reg 'rdi)))
                             (Instr 'movq (list (Imm 16) (Reg 'rsi)))
                             (Callq 'initialize 2)
                             (Instr 'movq (list (Global 'rootstack_begin) (Reg 'r15)))) '())
          (append
           (for/list ([i (in-range nrs)])
             (Instr 'movq (list (Imm 0) (Deref 'r15 (* 8 i)))))
           (if (= nrs 0) '()
               (list (Instr 'addq (list (Imm (* 8 nrs)) (Reg 'r15))))))
          (list (Jmp (symbol-append f 'start)))))))

(define (conclusion-is uc rspd nrs)
  (append
   (if (= nrs 0) '()
       (list (Instr 'subq (list (Imm (* 8 nrs)) (Reg 'r15)))))
   (if (= rspd 0) '()
       (list (Instr 'addq (list (Imm rspd) (Reg 'rsp)))))
   (reverse (for/list ([reg uc])
              (Instr 'popq (list (Reg reg)))))
   (list (Instr 'popq (list (Reg 'rbp))))))


;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
    ("shrink" ,shrink ,interp-Lfun,type-check-Lfun)
    ;;("partial" ,pe-Lvar ,interp-Lvar)
    ;;("residual" ,pe-Lvar-r ,interp-Lvar)
    ("uniquify" ,uniquify ,interp-Lfun,type-check-Lfun) 
    ("reveal functions" ,reveal-functions ,interp-Lfun-prime ,type-check-Lfun)
    ("limit functions" ,limit-functions ,interp-Lfun-prime ,type-check-Lfun) ;;have to work on this further
    ("expose allocation" ,expose-allocation ,interp-Lfun-prime ,type-check-Lfun) ;;done, not much was there
    ("uncover get!" ,uncover-get! ,interp-Lfun-prime ,type-check-Lfun)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lfun-prime ,type-check-Lfun)
    ("explicate control" ,explicate-control ,interp-Cfun ,type-check-Cfun)
    ("instruction selection" ,select-instructions ,interp-pseudo-x86-3)
    ;    ("constant propogation" ,constant-propogation ,interp-pseudo-x86-3)
    ;    ;; ("assign homes" ,assign-homes ,interp-x86-0)
    ("uncover live" ,uncover-live ,interp-pseudo-x86-3)
    ("build interference" ,build-interference ,interp-pseudo-x86-3)
    ("allocate registers" ,allocate-registers ,interp-pseudo-x86-3)
    ;    ("remove jumps" ,remove-jumps ,interp-pseudo-x86-2)
    ("build move bias", build-move-bias-graph ,interp-pseudo-x86-3)
    ("patch instructions" ,patch-instructions ,interp-pseudo-x86-3)
    ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-3)
    ))