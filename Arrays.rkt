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

    ;;;;;;;;;;;;;;;;;;;; ARRAY ;;;;;;;;;;;;;;;;;;;
    
    (expression ("newarray" "(" expression ")") newarray-exp) ;; newarray(size)
    (expression ("arrayref" "(" expression "," expression ")") arrayref-exp) ;; arrayref(array, index)
    (expression ("arrayset" "(" expression "," expression "," expression ")") arrayset-exp) ;; arrayset(array, index, value)
    (expression ("arraylength" "(" expression ")") arraylength-exp) ;; arraylength(array)
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

;;;;;ENVIRONMENT

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

;;; an expressed value is either a number, a boolean or a procval.


;;expval : datatype ;;expval? --> boolean
;;purpose: Define a datatype for various types of values
(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (proc-val 
   (proc proc?))
  (arr-val         ;<<<<<<<<<<<<<<< array ;;;;;;;;;;;;;;;;;;;
   (arr arr?)))

;;; extractors:


;;expval2num : ExpVal -> Int
;;expval -> Int throws error
;;Purpose: Extract number from given expval
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

;; expval => arr throws error
;; Purpose: extract arr from given expval
(define (expval2arr v)        ;<<<<<<<<<<<<<<< array ;;;;;;;;;;;;;;;;;;;;;
  (cases expval v
    (arr-val (arr) arr)
    (else (expval-extractor-error 'arr-val v))))

;;expval-extractor-error : Symbol ExpVal -> Error
;;symbol expval -> throws error
;;purpose throws an error when an invalid varient is used
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

;; proc : datatype
(define-datatype proc proc?
  (procedure
   (var (list-of symbol?))
   (body expression?)
   (envv voenv?)))


;;;;;;;;;;;;array;;;;;;;;;;;;;;;;;;;;;;

;;arr : datatype
;;  array
;;    size: number represents size/length of array
;;    first-loc: reference of the first item in the array
(define-datatype arr arr?
  (array
   (size number?)
   (first-loc reference?)))




;;;;;;;;;;;;;;;; the interpreter ;;;;;;;;;;;;;;;;

;; value-of-program : Program -> ExpVal
(define (value-of-program pgm)
  (begin
    (initialize-store!)
    (cases program pgm
      (a-program (exp1)
                 (value-of exp1 (empty-env))))))

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

    ;; new for call-by-ref: call function to decide if an arg is put in the store
    (call-exp (rator rands)
              (let [(proc (expval2proc (value-of rator env)))
                    (args (map (lambda (rand) (value-of-rand rand env)) rands))]
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
               (num-val 31))) ; a i don’t care value

;;;;;;;;;;;;;;;;;;;;;;;;;;; array operations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    ;; creates number of references equal to the given expression
    ;; an arr is created and an arr-val returned containing the given length and the first created reference
    ;; expression -> arr-val
    ;;               error
    (newarray-exp (exp1)
                  (let ((size-val (expval2num (value-of exp1 env))))
                    (if ( > size-val 0)
                        (let ((start-ref (newref 0)))
                          (let init-arr ((i 1))
                            (if (< i size-val)
                                (let ((ref (newref 0)))
                                  (init-arr (+ i 1)))
                                (arr-val (array size-val start-ref)))))
                        (eopl:error 'newarray-exp "invalid size: ~s" size-val))))

    ;; returns the value contained at the index given in exp2 of the arr-val given in exp1
    ;; expression expression -> expression
    ;;                          error
    (arrayref-exp (exp1 exp2)
                  (let ((a (expval2arr (value-of exp1 env)))
                         (index (expval2num (value-of exp2 env))))
                    (cases arr a
                      (array (size first-loc)
                             (if (and (>= index 0) (< index size))
                                 (deref (+ first-loc index))
                                 (eopl:error 'arrayref-exp "outside index range: ~s" index)))
                      (else
                       (eopl:error 'arrayref-exp "not an array: ~s" a)))))

    ;; mutates the value contained at the index exp2 of the arr-val exp1 to the value of exp3
    ;; expression expression expression -> expval
    ;;                                     error
    (arrayset-exp (exp1 exp2 exp3)
                  (let ((a (expval2arr (value-of exp1 env)))
                        (index (expval2num (value-of exp2 env)))
                        (val (value-of exp3 env)))
                    (cases arr a
                      (array (size first-loc)
                             (if (and (>= index 0) (< index size))
                                 (setref! (+ first-loc index) val)
                                 (eopl:error 'arrayref-exp "outside index range: ~s" index)))
                      (else
                       (eopl:error 'arrayref-exp "not an array: ~s" a)))))

    ;; returns the length/size of the arr-val exp1
    ;; expression -> num-val
    ;;               error
    (arraylength-exp (exp1)
                    (let ((a (expval2arr (value-of exp1 env))))
                      (cases arr a
                        (array (size first-loc)
                               (num-val size))
                        (else
                         (eopl:error 'arraylength-exp "Not an array: ~s" a)))))))

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
                           

;; new signature for call-by-ref

;; apply-procedure : proc (listof ref) -> expval 
;; Purpose: Apply the given procedure to the given values
(define (apply-procedure f vals)
  (cases proc f
    (procedure (params body envv)
               (let [(saved-env (vector-ref envv 0))]
                 (value-of body
                           (foldr (lambda (binding acc)
                                    (extend-env (car binding)
                                                (cadr binding) ;; no longer put in store
                                                acc))
                                  saved-env
                                  (map (lambda (p v) (list p v))
                                       params
                                       vals)))))))

;; new for call-by-ref

;; value-of-rand : expression environment -> Ref
;; Purpose: if the expression is a var-exp, then return the reference.
;; otherwise, evaluate the expression and pass a reference to a new
;; cell. 
(define (value-of-rand exp env)
  (cases expression exp
    (var-exp (var) (apply-env env var)) 
    (else
     (newref (value-of exp env)))))

;;;;;;   EVALUATION WRAPPERS

;; string -> a-program
;; Purpose: Parse the given extended LC-program
(define (parse p) (scan&parse p))

;; string -> ExpVal
;; Purpose: Evaluate the given extended LC-program
(define (eval string)
  (value-of-program (parse string)))

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

;; new/updated tests for call-by-ref

(check-equal? (eval "let a = 3
                     in let p = proc (x) set x = 4
                        in begin 
                             (p a); 
                             a 
                           end")
              (num-val 4))

(check-equal? (eval "let x = 0
                     in letrec f (x) = set x = +(x, 1)
                               g (a) = set x = +(x, 2)
                        in begin
                             (f x);
                             (g x);
                             x
                           end")
              (num-val 3))

;;             ;;
;; array tests ;;
;;             ;;

; newarray tests
(check-equal?
 (eval "newarray (4)")
 (arr-val (array 4 0)))

(check-equal? 
  (eval "newarray(10)") 
  (arr-val (array 10 0)))

(check-equal?
 (eval "newarray (100)")
 (arr-val (array 100 0)))

(check-equal?
 (eval "newarray (93)")
 (arr-val (array 93 0)))

(check-equal?
 (eval "newarray (171)")
 (arr-val (array 171 0)))

(check-equal?
 (eval "let a = newarray(5)
          in arrayref(a, 3)") 0)

; arrayref tests
(check-equal? 
  (eval "let a = newarray(3) in arrayref(a, 0)") 
  0) 

(check-equal? 
  (eval "let a = newarray(3) in arrayref(a, 2)") 
  0)

(check-equal? 
  (eval "let a = newarray(60) in arrayref(a, 43)") 
  0)

(check-equal? 
  (eval "let a = newarray(100) in arrayref(a, 99)") 
  0)

(check-equal? 
  (eval "let a = newarray(87) in arrayref(a, 9)") 
  0)

; arrayset tests
(check-equal? 
  (eval "
    let a = newarray(2) in
    begin
      arrayset(a, 0, 10);
      arrayset(a, 1, 20);
      arrayref(a, 0)
    end")
  (num-val 10))

(check-equal? 
  (eval "
    let a = newarray(5) in
    begin
      arrayset(a, 0, 10);
      arrayset(a, 1, 20);
      arrayset(a, 3, 15);
      arrayref(a, 1)
    end")
  (num-val 20))

(check-equal? 
  (eval "
    let a = newarray(30) in
    begin
      arrayset(a, 29, 67);
      arrayref(a, 29)
    end")
  (num-val 67))

(check-equal? 
  (eval "
    let a = newarray(100) in
    begin
      arrayset(a, 80, 50);
      arrayref(a, 80)
    end")
  (num-val 50))

(check-equal? 
  (eval "
    let a = newarray(150) in
    begin
      arrayset(a, 50, 82);
      arrayset(a, 11, 93);
      arrayset(a, 89, 23);
      arrayset(a, 120, 15);
      arrayset(a, 101, 848);
      arrayset(a, 3, 63);
      arrayset(a, 77, 2);
      arrayref(a, 89)
    end")
  (num-val 23))

(check-equal? 
  (eval "
    let a = newarray(150) in
    begin
      arrayset(a, 50, 6194);
      arrayset(a, 11, 8131);
      arrayset(a, 89, 5);
      arrayset(a, 120, 1523);
      arrayset(a, 101, 7163);
      arrayset(a, 3, 9274);
      arrayset(a, 77, 7854);
      arrayref(a, 77)
    end")
  (num-val 7854))

; arraylength tests
(check-equal? 
  (eval "let a = newarray(1) in arraylength(a)") 
  (num-val 1))

(check-equal? 
  (eval "arraylength(newarray(5))") 
  (num-val 5))

(check-equal? 
  (eval "let a = newarray(10) in arraylength(a)") 
  (num-val 10))

(check-equal? 
  (eval "let a = newarray(53) in arraylength(a)") 
  (num-val 53))

(check-equal? 
  (eval "let a = newarray(100) in arraylength(a)") 
  (num-val 100))

; More array tests with operations 
(check-equal? 
  (eval "
    let a = newarray(3) 
    in let b = newarray(7) 
       in arraylength(b)") 
  (num-val 7))

(check-equal? 
  (eval "
    let a = newarray(150) in
    begin
      arrayset(a, 50, 6194);
      arrayset(a, 11, 8131);
      arrayset(a, 89, 5);
      arrayset(a, 120, 1523);
      arrayset(a, 101, 7163);
      arrayset(a, 3, 9274);
      arrayset(a, 77, 7854);
      arrayref(a, 101)
    end")
  (num-val 7163))

(check-equal?
  (eval "
    let a = newarray(10) in
    begin
      arrayset(a, 2, 5);
      arrayset(a, 7, 15);
      +(arrayref(a, 2), arrayref(a, 7))
    end")
  (num-val 20))

(check-equal?
  (eval "
    let a = newarray(15) in
    begin
      arrayset(a, 5, 12);
      arrayset(a, 10, 8);
      -(arrayref(a, 5), arrayref(a, 10))
    end")
  (num-val 4))

(check-equal?
  (eval "
    let a = newarray(50) in
    begin
      arrayset(a, 17, 150);
      arrayset(a, 43, 100);
      arrayset(a, 25, +(arrayref(a, 17), arrayref(a, 43)));
      arrayref(a, 25)
    end")
  (num-val 250))

; Swap function 

; Swaps two elements in an array
; Checks the newly swapped locations to see if updated properly
(check-equal?
  (eval "
    let swap = proc (a)
                  proc (b)
                     proc (c)
                       let t = arrayref(a, b)
                       in let s = arrayref(a, c)
                          in begin
                               arrayset(a, b, s);
                               arrayset(a, c, t)
                             end
    
    in let a = newarray(2)
       in begin
            arrayset(a, 0, 100);
            arrayset(a, 1, 200);
            (((swap a) 0) 1);
            arrayref(a, 0)     
          end")
  (num-val 200))
