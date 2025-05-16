#lang eopl

(require rackunit)

;; Constructor for an empty stack
;; () -> stack
(define (empty-stack)
  (lambda (msg)
    (cond
      ((eq? msg 'pop) (eopl:error 'pop "Empty stack: nothing to pop"))
      ((eq? msg 'top) (eopl:error 'top "Empty stack: no values to check"))
      ((eq? msg 'empty?) #t)
      (else (eopl:error 'stack "Unknown operation")))))

;; Constructor for a stack with a new value pushed
;; stack value -> stack
(define (push stack val)
  (lambda (msg)
    (cond
      ((eq? msg 'pop) stack)
      ((eq? msg 'top) val)
      ((eq? msg 'empty?) #f)
      (else (eopl:error 'stack "Unknown operation")))))

;; Constructor that gets the stack after removing the top value
;; stack -> stack
(define (pop stack)
  (stack 'pop))

;; Observer that gets the top value of the stack
;; stack -> value
(define (top stack)
  (stack 'top))

;; Observer that checks if the stack is empty
;; stack -> boolean
(define (empty-stack? stack)
  (stack 'empty?))



;; Example stack for testing
(define exampleStack
  (push (push (push (empty-stack) 1) 2) 3)) ;; Using procedural stack


;; Basic tests 
(check-equal? '(5 3 2 1)
           (let ((stack1 (push (push (push (empty-stack) 1) 2) 3))) ;; Building stack using push
             (let ((stack2 (push stack1 5)))
               (list (top stack2) 
                     (top (pop stack2)) 
                     (top (pop (pop stack2))) 
                     (top (pop (pop (pop stack2))))))))

(check-equal? 2
           (top (pop exampleStack)))

(check-equal? 3
           (top exampleStack))

(check-equal? #f
           (empty-stack? exampleStack))

(check-equal? #t
           (empty-stack? (empty-stack)))

;; Bigger tests

(check-equal? 4
           (top (push (push (push (push (empty-stack) 1) 2) 3) 4)))

(check-equal? #t
           (let ((stack1 (push (push (push (push (empty-stack) 1) 2) 3) 4)))
             (empty-stack? (pop (pop (pop (pop stack1)))))))

(check-equal? '(7 6 5 4 3)
           (let ((stack1 (push (push (push (push (push (empty-stack) 3) 4) 5) 6) 7)))
             (list (top stack1) 
                   (top (pop stack1)) 
                   (top (pop (pop stack1))) 
                   (top (pop (pop (pop stack1))))
                   (top (pop (pop (pop (pop stack1))))))))

(check-equal? '(8 4)
           (let ((stack1 (push (push (push (empty-stack) 3) 4) 5)))
             (let ((stack2 (push (pop stack1) 8)))
               (list (top stack2)
                     (top (pop stack2))))))

(check-equal? '(9 8 7 6 5 4 3 2 1)
           (let ((stack1 (push (push (push (push (push (push (push (push (push (empty-stack) 1) 2) 3) 4) 5) 6) 7) 8) 9)))
             (list (top stack1) 
                   (top (pop stack1)) 
                   (top (pop (pop stack1))) 
                   (top (pop (pop (pop stack1)))) 
                   (top (pop (pop (pop (pop stack1))))) 
                   (top (pop (pop (pop (pop (pop stack1)))))) 
                   (top (pop (pop (pop (pop (pop (pop stack1))))))) 
                   (top (pop (pop (pop (pop (pop (pop (pop stack1)))))))) 
                   (top (pop (pop (pop (pop (pop (pop (pop (pop stack1))))))))))))