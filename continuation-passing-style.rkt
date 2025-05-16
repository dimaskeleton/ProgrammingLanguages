#lang eopl

(require rackunit "eopl-extras.rkt")

;;;;;;;;;;;;;;;; grammatical specification ;;;;;;;;;;;;;;;;

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    
    (comment ("%" (arbno (not #\newline))) skip)

    (identifier
     (letter (arbno (or letter digit "_" "-" "?"))) symbol)
    
    (number (digit (arbno digit)) number)
    
    (number ("-" digit (arbno digit)) number)
    ))
    
    
(define the-grammar
  '((program (expression) a-program)
    
    (expression (number) const-exp)

    (expression ("true") true-exp)

    (expression ("false") false-exp)

    (expression (identifier) var-exp)
    
    (expression("-" "(" expression "," expression ")") diff-exp)
    
    (expression ("zero?" "(" expression ")") zero?-exp)
    
    (expression
     ("if" expression "then" expression "else" expression) if-exp)
    
    (expression 
     ("let" (arbno identifier "=" expression) "in" expression) let-exp)
    
    (expression
     ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" expression)
               "in" expression) letrec-exp)
    
    (expression ("proc" "(" (arbno identifier) ")" expression) proc-exp)
    
    (expression ("(" expression (arbno expression) ")") call-exp)
    
    (expression
     ("begin" expression (arbno ";" expression) "end")
     begin-exp)

    ;; new for implicit-refs

    (expression ("set" identifier "=" expression)  set-exp)

    (expression ("+" "(" expression "," expression ")") sum-exp)


    ;------------------------------------------------------------CONTINUATION GRAMMAR--------------------------------------------------------------------
    
    (expression ("%cont" "(" identifier ")" expression) cont-exp)
    (expression ("call-cont" "(""(" expression ")" expression ")") call-cont-exp)
    (expression ("proc-cps" "(" (arbno identifier) "," expression ")" expression) proc-cps-exp)
    (expression ("call-proc-cps" "(" expression "," (arbno expression) "," expression ")") call-proc-cps-exp)
    (expression ("%set-cps" identifier "=" expression) set-cps-exp)
    (expression ("letrec-cps" (arbno identifier "(" (arbno identifier) "," expression ")" "=" expression) "in" expression) letrec-cps-exp)
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

;;;;;    ENVIRONMENT

(define-datatype environment environment?
  (empty-env)
  (extend-env 
   (bvar symbol?)
   (bval reference?)
   (saved-env environment?)))

(define (apply-env env search-sym)
  (cases environment env
    (empty-env ()
               (eopl:error 'apply-env "No binding for ~s" search-sym))
    (extend-env (var val saved-env)
                (if (eqv? search-sym var)
                    val
                    (apply-env saved-env search-sym)))))

;;;;;;; The store ;;;;;;;;;;;;;;;;;;;;

;; reference? : RacketVal -> Bool
(define (reference? v) (integer? v))


;; the-store: a Racket variable containing the current state of the
;; store.  Initially set to a dummy value.
(define the-store 'uninitialized)

;; empty-store : () -> store
(define (empty-store) '())

;; initialize-store! : () -> store
;; usage: (initialize-store!) sets the-store to the empty-store
(define (initialize-store!) (set! the-store (empty-store)))


;; newref : expval -> ref
(define (newref val)
  (let ((next-ref (length the-store)))
    (set! the-store (append the-store (list val))) 
    next-ref))

;; deref : ref -> expval
(define (deref ref) (list-ref the-store ref))

;; setref : ref expval -> expval
(define (setref! ref new-expval) (set! the-store (append (take the-store ref)
                                                         (list new-expval)
                                                         (drop the-store (add1 ref)))))



;;;;;;;;;;;;;;;; expressed values ;;;;;;;;;;;;;;;;

;;; an expressed value is either a number, a boolean or a procval OR a cont-val or proc-cps-val
(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (proc-val 
   (proc proc?))
  (cont-val      ;Cont----------------------------------------------------------------------------------------------------------------
   (cont cont?))
  (proc-cps-val
   (proc-cps proc-cps?)))

;;; extractors:

;; expval2num : ExpVal -> Int
;; expval --> Int throws error
;; Purpose: Extract number from given expval
(define (expval2num v)
  (cases expval v
    (num-val (num) num)
    (else (expval-extractor-error 'num-val v))))

;; expval --> Bool throws error
;; Purpose: Extract Boolean from given expval
(define (expval2bool v)
  (cases expval v
    (bool-val (bool) bool)
    (else (expval-extractor-error 'bool-val v))))

;; expval --> proc throws error
;; Purpose: Extract proc from given expval
(define (expval2proc v)
  (cases expval v
    (proc-val (proc) proc)
    (else (expval-extractor-error 'proc-val v))))

 ;----------------------------------------------------------------------------------------------------------------------------------------------
; expval --> cont throws error
; Purpose: Extract cont from given expval
(define (expval2cont v)
  (cases expval v
    (cont-val (cont) cont)
    (else (expval-extractor-error 'cont-val v))))

; expval --> proc-cps throws error
; Purpose: Extract proc-cps from given expval
(define (expval2proc-cps v)
  (cases expval v
    (proc-cps-val (proc-cps) proc-cps)
    (else (expval-extractor-error 'proc-cps-val v))))

;; symbol expval --> throws error
(define (expval-extractor-error variant value)
  (eopl:error 'expval-extractors "Looking for a ~s, given ~s"
              variant value))


;;;;;;;;;;;;;;;; procedures ;;;;;;;;;;;;;;;;

;; Any --> Boolean
;; Purpose: Determine if given value is a vector with a single environment
(define (voenv? penv)
  (and (vector? penv)
       (= (vector-length penv) 1)
       (environment? (vector-ref penv 0))))

(define-datatype proc proc?
  (procedure
   (var (list-of symbol?))
   (body expression?)
   (envv voenv?)))

;--------------------------------------------------------------------------------------------------------------------------------------------
; Data type for a cont
(define-datatype cont cont?
  (continuation
   (var symbol?)
   (body expression?)
   (env environment?)))

; Data type for a proc-cps
(define-datatype proc-cps proc-cps?
  (cps-procedure
   (var (list-of symbol?))
   (body expression?)
   (cont proc?)
   (envv voenv?)))
   

;;;;;;;;;;;;;;;; the interpreter ;;;;;;;;;;;;;;;;

;; value-of-program : Program -> ExpVal
(define (value-of-program pgm)
  (begin
    (initialize-store!)
    (cases program pgm
      (a-program (exp1)
                 (value-of exp1 (empty-env))))))

; end/identity continuation
(define (end-cont)
  (cont-exp 'v (var-exp 'v)))

; cps conversion of a given program
; string(implicit-refs program) -> string(implicit-refs program)
(define (cps-of-program pgm)
  (cases program (parse pgm)
    (a-program (exp1)
               (unparse (cps-of exp1 (cont-exp 'v-00 (var-exp 'v-00)))))))

;; value-of : Exp * Env -> ExpVal
(define (value-of exp env)
  (cases expression exp
    
    (const-exp (num) (num-val num))

    (true-exp () (bool-val #t))

    (false-exp () (bool-val #f))
    
    (var-exp (var) (deref (apply-env env var)))
    
    (diff-exp (exp1 exp2)
              (let ((num1 (expval2num (value-of exp1 env)))
                    (num2 (expval2num (value-of exp2 env))))
                (num-val (- num1 num2))))
    
    (zero?-exp (exp1)
               (let ((val1 (expval2num (value-of exp1 env))))
                 (if (zero? val1)
                     (bool-val #t)
                     (bool-val #f))))
    
    (if-exp (exp1 exp2 exp3)
            (let ((val1 (value-of exp1 env)))
              (if (expval2bool val1)
                  (value-of exp2 env)
                  (value-of exp3 env))))
    
    (let-exp (vars exps body)       
             (let [(vals (map (lambda (e) (value-of e env)) exps))]
               (value-of body
                         (foldr (lambda (var val acc)
                                  (extend-env var (newref val) acc))
                                env
                                vars
                                vals))))

    (proc-exp (params body)
              (proc-val (procedure params body (vector env))))
    
    (call-exp (rator rands)
              (let [(proc (expval2proc (value-of rator env)))
                    (args (map (lambda (rand) (value-of rand env)) rands))]
                (apply-procedure proc args)))
               
                
                          

                
              

    (letrec-exp (names params bodies letrec-body)
                (value-of letrec-body (mk-letrec-env names params bodies env)))

    (begin-exp (exp exps)
               (foldl (lambda (e v) (value-of e env)) (value-of exp env) exps))

    (sum-exp (exp1 exp2)
             (let ((num1 (expval2num (value-of exp1 env)))
                   (num2 (expval2num (value-of exp2 env))))
               (num-val (+ num1 num2))))
    
    (set-exp (var exp1)
             (begin
               (setref! (apply-env env var) (value-of exp1 env))
               (num-val 31))) ; a don’t care value

    (cont-exp (param body)
              (cont-val (continuation param body env)))

    (call-cont-exp (rator rand)
                   (let [(proc (expval2proc (value-of rator env)))
                         (arg (value-of rand env))]
                     (apply-procedure proc (list arg))))

    (proc-cps-exp (params cont body)
                  (let [(proc (expval2proc (value-of cont env)))]
                    (proc-cps-val (cps-procedure params body proc (vector env)))))

    (call-proc-cps-exp (rator rands cont)
                       (let [(proc-cps (expval2proc-cps (value-of rator env)))
                             (args (map (lambda (rand) (value-of rand env)) rands))
                             (cont (expval2proc (value-of cont env)))]
                         (apply-cps-procedure proc-cps args cont)))

    (set-cps-exp (var exp1)
                 (begin
                   (setref! (apply-env env var)(value-of exp1 env))
               (num-val 32))) ; a don’t care value

    (letrec-cps-exp (names params conts bodies letrec-cps-body)
                    (value-of letrec-cps-body (mk-letrec-cps-env names params conts bodies env)))
    ))

; Purpose: Returns an ast back into a string of implicit-refs code
; ast -> string(implicit-refs program)
(define (unparse ast)
  (cases expression ast
    (const-exp (num) (number->string num))
    (true-exp () "true")
    (false-exp () "false")
    (var-exp (var) (symbol->string var))
    (diff-exp (exp1 exp2)
              (string-append "-(" (unparse exp1) " , " (unparse exp2) ")"))
    (zero?-exp (exp1) (string-append "zero?(" (unparse exp1) ")"))
    (if-exp (exp1 exp2 exp3)
            (string-append "if " (unparse exp1) " then " (unparse exp2) " else " (unparse exp3)))
    (let-exp (vars exps body)
             (string-append "let " (apply string-append (map (lambda (v e)
                                                              (string-append (symbol->string v) " = " (unparse e)))
                                                            vars
                                                            exps))
                            " in " (unparse body)))
    (proc-exp (params body)
              (string-append "proc (" (apply string-append (map (lambda (v)
                                                                  (string-append " " (unparse v) " "))
                                                                params))
                             ") " (unparse body)))
    (call-exp (rator rands)
              (string-append "(" (unparse rator) (apply string-append (map (lambda (v)
                                                                             (string-append " " (unparse v) " "))
                                                                           rands))
                             ")"))
    (letrec-exp (names params bodies letrec-body)
                (string-append "letrec" (apply string-append (map (lambda (n p b)
                                                                     (string-append " " (unparse n) " (" (unparse p) ") " "= " (unparse b)))
                                                                  names
                                                                  params
                                                                  bodies))
                               " in " (unparse letrec-body)))
    (begin-exp (exp exps)
               (string-append "begin " (unparse exp) (apply string-append (map (lambda (e)
                                                                                 (string-append "; " (unparse e)))
                                                                               exps))
                              " end"))
    (sum-exp (exp1 exp2)
             (string-append " +(" (unparse exp1) " , " (unparse exp2) ")"))
    (set-exp (var exp1)
             (string-append "set " (symbol->string var) " = " (unparse exp1)))
    
    (cont-exp (param body)
              (string-append "proc ("(symbol->string param) ") " (unparse body)))
    
    (call-cont-exp (rator rand)
                   (string-append "call-cont((" (unparse rator) ")" (unparse rand) ")"))

    (proc-cps-exp (params body cont)
                  (string-append "proc-cps(" (apply string-append (map(lambda(p)
                                                                        (symbol->string p))
                                                                      params))
                                                    "," (unparse cont) ")" (unparse body)))
    (call-proc-cps-exp (rator rands cont)
                       (string-append "call-proc-cps(" (unparse rator) "," (apply string-append (map(lambda(r)
                                                                                                  (unparse r))
                                                                                                rands))
                                      "," (unparse cont) ")"))
    (set-cps-exp (var exp1)
                 (string-append "set " (unparse var) " = " (unparse exp1)))

    (letrec-cps-exp (names params conts bodies letrec-cps-body)
                    (string-append "letrec-cps " (apply string-append (map (lambda (n p c b)
                                                                             (string-append
                                                                              (symbol->string n)"("
                                                                              (apply string-append
                                                                                     (map (lambda (sym)
                                                                                            (string-append (symbol->string sym) " "))
                                                                                          p)) "," (unparse c) ") = "
                                                                                              (unparse b)))
                                                                           names params conts bodies))
                                   " in " (unparse letrec-cps-body)))
    
    ))


  
;; (listof symbol) (listof (listof symbol)) (listof expression) environment --> environment
;; Purpose: Add the proc-vals for the given procedures in the given environment
(define (mk-letrec-env names params bodies env)
  (let* [(temp-proc-vals (map (lambda (p b)
                                (proc-val (procedure p b (vector (empty-env)))))
                              params
                              bodies))
         (new-env (foldl (lambda (name proc env)
                           (extend-env name
                                       (newref proc)
                                       env))
                         env
                         names
                         temp-proc-vals))]
    (begin
      (for-each (lambda (p)
                  (cases proc p
                    (procedure (p b ve)
                               (vector-set! ve 0 new-env))))
                (map (lambda (p) (expval2proc p))
                     temp-proc-vals))
      new-env)))

; (listof symbol) (listof (listof symbol))(listof expression)(listof expression)environment -> environment
; Purpose: Add the proc-cps-vals for the given cps-procedures in the given environment
(define (mk-letrec-cps-env names params conts bodies env)
  (let* ([temp-proc-vals 
          (map (lambda (p b c)
                 (proc-val (procedure p b (vector (empty-env)))))
               params
               bodies
               conts)]
         [new-env
          (foldl (lambda (name proc acc)
                   (extend-env name (newref proc) acc))
                 env
                 names
                 temp-proc-vals)]
         [new-new-env
          (foldl (lambda (param proc acc)
                   (extend-env (car param) (newref (num-val 39)) acc))
                 new-env
                 params
                 temp-proc-vals)]
         [cps-proc-vals
          (map (lambda (p)
                 (cases proc (expval2proc p)
                   (procedure (p b ve)
                     (proc-cps-val
                      (cps-procedure p
                                     b
                                     (expval2proc (value-of (proc-exp (list 'v-00) (var-exp 'v-00)) new-new-env))
                                     (vector new-new-env))))))
               temp-proc-vals)])
    (set! new-new-env
          (foldl (lambda (name proc acc)
                   (extend-env name (newref proc) acc))
                 new-new-env
                 names
                 cps-proc-vals))

    (for-each
     (lambda (p)
       (cases proc-cps p
         (cps-procedure (p b c ve)
                        (vector-set! ve 0 new-new-env))))
     (map expval2proc-cps cps-proc-vals))
    new-new-env))
 

;; apply-procedure : proc (listof expval) -> expval
;; Purpose: Apply the given procedure to the given values
(define (apply-procedure f vals)
  (cases proc f
    (procedure (params body envv) 
               (let [(saved-env (vector-ref envv 0))]
                 (value-of body
                           (foldr (lambda (binding acc)
                                    (extend-env (car binding)
                                                (newref (cadr binding))
                                                acc))
                                  saved-env
                                  (map (lambda (p v) (list p v))
                                       params
                                       vals)))))))

; apply-continuation: cont expval -> expval
; Purpose: apply the given continuation to the given value
(define (apply-continuation f val)
  (cases cont f
    (continuation (param body env)
                  (value-of body
                            (extend-env param (newref val) env)
                            ))))

; apply-cps-procedure: proc-cps (listof expval) proc -> expval
; Purpose: apply the given cps-procedure to the given values with respect to the given cont procedure
(define (apply-cps-procedure f vals cont1)
  (cases proc-cps f
    (cps-procedure (params body cont envv)
                   (let [(saved-env (vector-ref envv 0))]
                     (apply-procedure cont1
                                         (list(value-of body
                                                   (foldr (lambda (binding acc)
                                                            (extend-env (car binding)
                                                                        (newref (cadr binding))
                                                                        acc))
                                                          saved-env
                                                          (map (lambda (p v) (list p v))
                                                               params
                                                               vals)))))))))
    
;;;;;;   EVALUATION WRAPPERS

;; string -> a-program
;; Purpose: Parse the given extended LC-program
(define (parse p) (scan&parse p))

;; string -> ExpVal
;; Purpose: Evaluate the given extended LC-program
(define (eval string)
  (value-of-program (parse string)))

;--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
; get-set-v: expression -> symbol (throw error)
; Purpose: return var of given set
(define (get-set-v exp)
  (cases expression exp
    (set-exp (var exp1)
             var)
    (else (eopl:error 'get-set-v "Not a set-exp ~s " exp))))

; get-set-e: expression -> expression (throw error)
; Purpose: return exp of a given set 
(define (get-set-e exp)
  (cases expression exp
    (set-exp (var exp1)
             exp1)
    (else (eopl:error 'get-set-e "Not a set-exp ~s " exp))))

; noncall?: expression -> boolean
; Purpose: Determine if given expression is considered a noncall or is in cps
(define (noncall? exp)
  (cases expression exp
    (const-exp (num) #t)
    (true-exp () #t)
    (false-exp () #t)
    (var-exp (var) #t)
    (proc-cps-exp (params body cont) #t)
    (call-proc-cps-exp (rator rands cont) #t)
    (set-cps-exp (var exp1) #t)
    (letrec-cps-exp (names params conts bodies letrec-body) #t)
    (cont-exp (param body) #t)
    (call-cont-exp (rator rand) #t)
    (else #f)))

; find-call: (listof expressions) -> number
; Purpose: return the index of the first occurence of a function call in the given list
(define (find-call exps)
  (let ([notfound? #t] ; Starts as true, tracks if a function call has been found
        [curr 0]       ; Starts as 0, tracks the current index until notfound? == false
        [res 0])       ; Starts as 0, holds the index of the first occurence of a function call, becomes the return value 
    (for-each (lambda (e) (cond [(noncall? e)
                                 (set! curr (add1 curr))] 
                                [notfound?
                                 (begin
                                   (set! res curr)
                                   (set! notfound? #f))]
                                [else
                                 (set! curr (add1 curr))]))
              exps)
    res))

; isset?: expression -> boolean
; Purpose: determine if a given expression is a set-exp
(define (isset? exp)
  (cases expression exp
    (set-exp (var exp1)
             #t)
    (else
     #f)))

; cps-of: expression continuation -> expression
; Purpose: reformat the given expression into cps with respect to given continuation
(define (cps-of exp k)
  (cases expression exp
    (const-exp (num) (call-cont-exp k (const-exp num)))
    (true-exp () (call-cont-exp k (true-exp)))
    (false-exp () (call-cont-exp k (false-exp)))
    (var-exp (var) (call-cont-exp k (var-exp var)))
    (diff-exp (exp1 exp2)
              (cond [(and (noncall? exp1) (noncall? exp2))
                     (call-cont-exp k (diff-exp exp1 exp2))]
                    [(noncall? exp1)
                     (let ([v (generate-symbol 'v)])
                       (cps-of exp2 (cont-exp v (cps-of (diff-exp exp1 (var-exp v)) k))))]
                    [(noncall? exp2)
                     (let ([v (generate-symbol 'v)])
                       (cps-of exp1 (cont-exp v (cps-of (diff-exp (var-exp v) exp2) k))))]
                    [else
                     (let ([v (generate-symbol 'v)])
                       (cps-of exp1 (cont-exp v (cps-of (diff-exp (var-exp v) exp2) k))))]))
    (zero?-exp (exp1)
               (cond [(noncall? exp1)
                      (call-cont-exp k (zero?-exp exp1))]
                     [else
                      (let ([v (generate-symbol 'v)])
                        (cps-of exp1 (cont-exp v (cps-of (zero?-exp (var-exp v)) k))))]))
    (if-exp (exp1 exp2 exp3)
            (cond [(noncall? exp1)
                   (if-exp exp1 (cps-of exp2 k) (cps-of exp3 k))]
                  [else
                   (let ([v (generate-symbol 'v)])
                     (cps-of exp1 (cont-exp v (if-exp (var-exp v) (cps-of exp2 k) (cps-of exp3 k)))))]))
    (let-exp (vars exps body)
             (let-exp vars
                      (map (lambda (e) (cps-of e k))
                                exps)
                      (cps-of body k)))
    (proc-exp (params body)
              (call-cont-exp k (proc-cps-exp params (cps-of body k) k)))
    
    (call-exp (rator rands)
              
              (cond [(andmap noncall? rands)
                     (call-proc-cps-exp rator rands k)]
                    [else
                     (let ([v (generate-symbol 'v)]
                           [ref (find-call rands)])
                       (cps-of (list-ref rands ref) (cont-exp v (cps-of (call-proc-cps-exp rator
                                                                                             (append (take rands ref)
                                                                                                     (list (var-exp v))
                                                                                                     (drop rands (add1 ref)))
                                                                                             k) k))))]))

    (call-proc-cps-exp (rator rands cont)
                       (cond [(andmap noncall? rands) 
                              (call-proc-cps-exp rator rands k)]
                             [else
                              (let ([v (generate-symbol 'v)]
                                    [ref (find-call rands)])
                                (cps-of (list-ref rands ref) (cont-exp (v) (cps-of (call-proc-cps-exp rator
                                                                                                      (append (take rands ref)
                                                                                                              (list (var-exp v))
                                                                                                              (drop rands (add1 ref)))
                                                                                                      k) k))))]))
    
    (letrec-exp (names params bodies letrec-body)
                (letrec-cps-exp names
                                params
                                (build-list (length names) (lambda (x) k))
                                (map (lambda (b)
                                       (cps-of b k))
                                     bodies)
                                (cps-of letrec-body k)))
    
    (begin-exp (exp exps)
               (cond [(and (noncall? exp) (andmap noncall? exps))
                      (call-cont-exp k (begin-exp exp exps))]
                     [(noncall? exp)
                      (let ([v (generate-symbol 'v)]
                            [ref (find-call exps)]
                            )
                        (cond [(isset? (list-ref exps ref))
                               (cps-of (get-set-e (list-ref exps ref) (cont-exp v (cps-of
                                                                          (begin-exp exp
                                                                                     (append (take exps ref)
                                                                                             (list (set-cps-exp (get-set-v (list-ref exps ref)) (var-exp v)))
                                                                                             (drop exps (add1 ref))))
                                                                          k))))]
                              [else
                               (cps-of (list-ref exps ref) (cont-exp v (cps-of (begin-exp exp
                                                                                            (append (take exps ref)
                                                                                                    (list (var-exp v))
                                                                                                    (drop exps (add1 ref))))
                                                                                 k)))]))]
                     [else 
                      (let ([v (generate-symbol 'v)])
                        (cond [(isset? exp)
                               (cps-of (get-set-e exp) (cont-exp v (cps-of
                                                                      (begin-exp (set-cps-exp (get-set-v exp) (var-exp v))
                                                                                 exps)
                                                                      k)))]
                              [else
                               (cps-of exp (cont-exp v (cps-of (begin-exp (var-exp v) exps) k)))]))]))
    (sum-exp (exp1 exp2)
             (cond [(and (noncall? exp1) (noncall? exp1))
                     (call-cont-exp k (sum-exp exp1 exp2))]
                    [(noncall? exp1)
                     (let ([v (generate-symbol 'v)])
                       (cps-of exp2 (cont-exp v (cps-of (sum-exp exp1 (var-exp v)) k))))]
                    [(noncall? exp2)
                     (let ([v (generate-symbol 'v)])
                       (cps-of exp1 (cont-exp v (cps-of (sum-exp (var-exp v) exp2) k))))]))

    (else
     exp)))


 



;;;;; EXAMPLES OF EVALUATION

(check-equal? (eval "if zero?(1) then 1 else 2")
              (num-val 2))

(check-equal? (eval "-(15, 10)")
              (num-val 5))

(check-equal? (eval "let x = 10 in if zero?(-(x, x)) then x else 2")
              (num-val 10))

(check-equal? (eval "let decr = proc (a) -(a, 1) in (decr 30)")
              (num-val 29))
 
(check-equal? (eval "( proc (g) (g 30) proc (y) -(y, 1))")
              (num-val 29))

(check-equal? (eval "let x = 200
                     in let f = proc (z) -(z, x) 
                        in let x = 100 
                           in let g = proc (z) -(z, x) 
                              in -((f 1), (g 1))")
              (num-val -100))

(check-equal? (eval "let sum = proc (x) proc (y) -(x, -(0, y)) in ((sum 3) 4)")
              (num-val 7))

(check-equal? (eval "let sum = proc (x) proc (y) -(x, -(0, y))
                     in letrec sigma (n) = if zero?(n)
                                           then 0
                                           else ((sum n) (sigma -(n, 1)))
                        in (sigma 5)")
              (num-val 15))

(check-equal? (eval "letrec even(n) = if zero?(n)
                                      then zero?(n)
                                      else if zero?(-(n, 1))
                                           then zero?(n)
                                           else (even -(n, 2))
                     in (even 501)")
              (bool-val #f))

(check-equal? (eval "let a = 3
                     in let p = proc (x) set x = 4
                        in begin 
                             (p a); 
                             a 
                           end")
              (num-val 3))

(check-equal? (eval "let x = 0
                     in letrec f (x) = set x = +(x, 1)
                               g (a) = set x = +(x, 2)
                        in begin
                             (f x);
                             (g x);
                             x
                           end")
              (num-val 2))
