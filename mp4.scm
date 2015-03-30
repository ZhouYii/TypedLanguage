#lang eopl
(require trace/calltrace-lib)


;=================================Spec&Grammar=====================================

;;scanner
;;referred from textbook Appendix B
(define q1-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit))) symbol)
    (number (digit (arbno digit)) number)
    (arith-op ((or (or "-" "+") (or "*" "/"))) symbol)
    (compare-op ((or ">" "<")) symbol)
    ))

;;parser
;;referred from textbook Appdendix B
(define q1-grammar
  '((expression (number) num-exp)
    (expression (identifier) var-exp)
    (expression ("let" (arbno identifier "=" expression) "in" expression) let-exp) 
    (expression ("letrec" (arbno identifier "=" expression) "in" expression) letrec-exp)
    (expression ("proc" "(" (arbno identifier) ")" expression) proc-exp)
    (expression ( "(" expression (arbno expression) ")") exp-exp)
    (expression ("newref" "(" expression ")") newRef-exp)
    (expression ("set" identifier expression)set-exp)
    (expression ("begin" expression (arbno ";" expression) "end")begin-exp)
    (expression ("if" expression "then" expression "else" expression)if-exp)
    (expression (arith-op "(" expression (arbno "," expression) ")")arith-exp)
    (expression (compare-op "(" expression "," expression ")") compare-exp)
    (expression ("=" "(" expression "," expression ")") compare-equ-exp)
    (expression ("true") true-exp)
    (expression ("false") false-exp)
    (expression ("newpair" "(" expression "," expression")") newpair-exp)
    (expression ("first" "(" expression ")") first-exp) 
    (expression ("second" "(" expression")") second-exp)
    ))

;;sllgen from textbook appendix B
(sllgen:make-define-datatypes q1-spec q1-grammar)
(define scan&parse
  (sllgen:make-string-parser q1-spec q1-grammar))
;=================================Interpreter=====================================

;;Copy from MP instruction
(define-datatype type type?
  (int-type)
  (bool-type)
  (proc-type
   (arg-type (list-of type?))
   (return-type type?))
  (pair-type
   (first-type type?)
   (second-type type?))
  (tvar-type
   (sym symbol?))
  (bad-type))

;;Add pair-val
(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (proc-val
   (proc proc?))
  (pair-val
   (first expval?)
   (second expval?)))

(define typeCheck
  (lambda (ty1 ty2)
    (if(equal? ty1 ty2)
       #t
       #f)))

;;Refered from slides
(define-datatype proc proc?
  (procedure
   (bvar list?)
   (body expression?)
   (env environment?)))

;;define environment; code from slides and textbook pg.86 figure 3.12
(define-datatype environment environment?
  (empty-env)
  (extend-env 
   (bvar symbol?)
   (bval type?)
   (next-env environment?))
  (extend-env-rec*
   (proc-names list?)
   (proc-vars list?)
   (proc-bodies list?)
   (next-env environment?)))

;;Refered from slides
(define apply-env
  (lambda (search-sym env)
    (cases environment env
      (empty-env ()
                 search-sym)
      (extend-env (bvar bval next-env)
                  (if (eqv? search-sym bvar)
                      bval
                      (apply-env  search-sym next-env)))
      (extend-env-rec* (procedureNamelist procedureVarList procedureBodyList next-env)
                       (cond 
[(location search-sym procedureNamelist)
                          => (lambda (n)
                               (if(null?(list-ref procedureVarList n))
                                  (type-of-exp (list-ref procedureBodyList n) next-env )
                                  (proc-val
                                   (procedure 
                                    (list-ref procedureVarList n)
                                    (list-ref procedureBodyList n)
                                    env))))]
                         (else (apply-env search-sym  next-env)))))))

;;;;refered from book & https://github.com/mwand/eopl3/blob/master/chapter4/explicit-refs/environments.scm
(define location
  (lambda (sym syms)
    (cond
      ((null? syms) #f)
      ((eqv? sym (car syms)) 0)
      ((location sym (cdr syms))
       => (lambda (n) 
            (+ n 1)))
      (else #f))))

;;code from book pg.70
(define expval->num
  (lambda (v)
    (cases expval v
      (num-val (num) num)
      (else (expval-extractor-error 'num v)))))

;;code from book pg.70
(define expval->bool
  (lambda (v)
    (cases expval v
      (bool-val (bool) bool)
      (else 0))))

;;refered from: https://github.com/mwand/eopl3/blob/master/chapter4/explicit-refs/data-structures.scm
(define expval->proc
  (lambda (v)
    (cases expval v
      (proc-val (proc) proc)
      (else (expval-extractor-error 'proc v)))))

;;refered from: https://github.com/mwand/eopl3/blob/master/chapter4/explicit-refs/data-structures.scm
(define expval-extractor-error
  (lambda (variant value)
    value))

(define gensym
  (let ([counter 0])
    (begin (string->symbol (string-append "t" (number->string counter)))
           (set! counter (+ 1 counter)))))
    

;=====================================type-of-exp========================================
(define type-of-exp
  (lambda (exp env)
    (cond 
      [(type? exp) exp]
      [else 
    (cases expression exp
      (num-exp (number) (int-type))
      
      (var-exp (var) (apply-env var env))
      
      (true-exp () (bool-type))
      
      (false-exp () (bool-type))
      
      (let-exp (var-list exp1-list exp2)
               (type-of-exp exp2
                        (add-env var-list exp1-list env)))
      
      ;(letrec-exp (var-list exp1-list body)(type-of-exp-letrec var-list exp1-list body env state) );;;TO DO
      
      
      (proc-exp(var-list exp)
               (let* [(var-type-list (getNewTvar var-list))
                     (result-type (type-of-exp exp (add-env var-list var-type-list env)))]
                 (proc-type var-type-list result-type)))
      
      (exp-exp(rator rand-list)
              (let* ([exp-list (cons rator rand-list)]
                     [exp-list-length (length exp-list)]
                     [env-list (replicate env exp-list-length)]
                     [value-list (map type-of-exp exp-list env-list)])
                (list-last value-list)))  
              
      ;(begin-exp (exp1 exp2-list) (type-of-exp-begin exp1 exp2-list env state));;TO DO
      
      (if-exp(exp1 exp2 exp3)
             (let [(ty1 (type-of-exp exp1 env))
                   (ty2 (type-of-exp exp2 env))
                   (ty3 (type-of-exp exp3 env))]
               (if (and (typeCheck ty1 (bool-type))(typeCheck ty2 ty3))
                   ty2
                   (bad-type))))
      
      (arith-exp(arith-op exp1 exp2)
                (let* [(ty1 (type-of-exp exp1 env))
                      [exp-list-length (length exp2)]
                      [env-list (replicate env exp-list-length)]
                      (ty2-list (map type-of-exp exp2 env-list))
                      (int-list (replicate (int-type) exp-list-length))
                      (ty2-typeCheck (map typeCheck ty2-list int-list))]
                  (if (and (and (typeCheck ty1 (int-type))(typeCheck (type-of-exp (car exp2) env) (int-type))) (andBool ty2-typeCheck))
                    ty1
                   (bad-type))))
      
      (compare-exp(compare-op exp1 exp2)
                     (let [(ty1 (type-of-exp exp1 env))
                      (ty2 (type-of-exp exp2 env))]
                  (if (and (typeCheck ty1 (int-type))(typeCheck ty2 (int-type)))
                   (bool-type)
                   (bad-type))))
                  
      (compare-equ-exp(exp1 exp2)
                         (let [(ty1 (type-of-exp exp1 env))
                      (ty2 (type-of-exp exp2 env))]
                  (if (and (typeCheck ty1 (int-type))(typeCheck ty2 (int-type)))
                   (bool-type)
                   (bad-type))))
      
      (newpair-exp (exp1 exp2) 
                   (let [(ty1 (type-of-exp exp1 env))
                         (ty2 (type-of-exp exp2 env))]
                     (pair-type ty1 ty2)))
      
      (first-exp(exp) 
                (let [(ty1 (type-of-exp exp env))]
                 (cases type ty1
                   (pair-type(first second) first)
                   (else (bad-type)))))
      
      (second-exp (exp)  
                    (let [(ty1 (type-of-exp exp env))]
                 (cases type ty1
                   (pair-type(first second) second)
                   (else (bad-type)))))
      
      (else exp))])))


(define andBool
  (lambda (exp-list)
    (if (null? (cdr exp-list))
        (cdr exp-list)
        (and (car exp-list) (andBool (cdr exp-list))))))

(define getNewTvar
  (lambda (var-list)
    (map (lambda (list) (tvar-type gensym) )var-list)))


; Replicates the given element n times, returning a list.
(define replicate
  (lambda (element n)
    (cond
      ((zero? n)
        '())
      (else
        (cons element (replicate element (- n 1)))))))

; Returns the last element of the given list.
(define list-last
  (lambda (l)
    (if (equal? (length l) 1)
      (car l)
      (list-last (cdr l)))))

; A fold left implementation.
(define fold-left
  (lambda (function the-list)
    (cond
      ((eqv? (length the-list) 1)
        (function (car the-list)))
      ((eqv? (length the-list) 2)
        (function (car the-list) (cadr the-list)))
      (else
        (let ([lhs (car the-list)]
              [rhs (cadr the-list)])
          (fold-left function (cons (function lhs rhs) (cddr the-list))))))))

(define type-of-exp-letrec
  (lambda(functionNamesList exp-list body env state)
    (let ([recEnv (letrec-getEnvRec functionNamesList exp-list env state)]
          [extendEnv (letrec-getEnv functionNamesList exp-list env state)])
      (type-of-exp body 
                (getRecEnv recEnv extendEnv) 1))))

(define getRecEnv
  (lambda (revEnv extendEnv)
    (cases environment revEnv
      (extend-env-rec* (exp1 exp2 exp3 oldEnv)
                       (extend-env-rec*
                        exp1 
                        exp2
                        exp3
                        extendEnv))
      (else extendEnv))))

(define letrec-getEnv
  (lambda (functionNamesList exp-list env state)
    (if(null? (cdr exp-list))
       (cases expression (car exp-list)
         (proc-exp(var-list exp) env)
         (else (extend-env (car functionNamesList) (type-of-exp (car exp-list) env state) env)))
       (cases expression (car exp-list)
         (proc-exp(var-list exp) env)
         (else (letrec-getEnv (cdr functionNamesList) (cdr exp-list) (extend-env (car functionNamesList) (type-of-exp (car exp-list) env state) env ) state))))))

(define letrec-getEnvRec
  (lambda (functionNamesList exp-list env state)
    (if(null? (cdr exp-list))
       (cases expression (car exp-list)
         (proc-exp(var-list exp) (extend-env-rec* functionNamesList (list var-list) exp-list env))
         (else env))
       (cases expression (car exp-list)
         (proc-exp(var-list exp) 
                  (let ([prevEnv (letrec-getEnvRec (cdr functionNamesList)(cdr exp-list) env state)])
                    (cases environment prevEnv
                      (extend-env-rec* (nameList varList bodyList env)
                                       (extend-env-rec*
                                        (append nameList (list (car functionNamesList)))
                                        (append varList (list var-list))
                                        (append bodyList (list (car exp-list)))
                                        env))
                      (else env))))
         (else  env)))))





(define type-of-exp-begin
  (lambda (exp1 exps env state)
    (letrec
        ((type-of-exp-begins
          (lambda (e1 es)
            (let ([v1 (type-of-exp e1 env state)])
              (if (null? es)
                  v1
                  (type-of-exp-begins (car es) (cdr es)))))))
      (type-of-exp-begins exp1 exps))))

(define add-env
  (lambda (var-list exp1-list env)
    (let ([newtype (type-of-exp (car exp1-list) env)])
      (if (null? (cdr var-list)) 
          (extend-env (car var-list) newtype env)
          (add-env (cdr var-list) (cdr exp1-list) (extend-env (car var-list) newtype env))))))

(define add-env-proc
  (lambda (var-list exp1-list env state)
    (if (null? (cdr var-list))
        (cond 
          [(expression? (car exp1-list)) 
           (extend-env (car var-list) (type-of-exp (car exp1-list) env state) env)]
          [else (extend-env (car var-list) (type-of-exp(car exp1-list) env state) env)])
        (cond 
          [(expression? (car exp1-list)) 
           (extend-env (car var-list) (type-of-exp (car exp1-list) env state) (add-env-proc (cdr var-list) (cdr exp1-list) env state))]
          [else (extend-env (car var-list) (type-of-exp (car exp1-list) env state) (add-env-proc (cdr var-list) (cdr exp1-list) env state))]))))

;;================Two cases to resolve letrec and curry==============
(define apply-procedure
  (lambda (proc1 arg state)
    (cases proc proc1
      (procedure (var body saved-env)
                 (let ((new-env (add-env-proc var arg saved-env state)))
                   (type-of-exp body new-env state))))))



;==============================Wrap Func=================================
(define type-of
  (lambda (exp)
    (type-of-exp (scan&parse exp) (empty-env))))

;=====================================Test========================================
(trace type-of)
(trace type-of-exp)
(trace add-env)
(trace scan&parse)
(trace getNewTvar)
(trace fold-left)
(trace typeCheck)
(trace andBool)
;(trace addCounter)
;(trace gensym)


;(type-of "1")
;(type-of "true")
;(type-of "let x= newpair (1,2) in first (x)");int-type
;(type-of "let f = proc (x) +(x,1) in (f 2)");int-type
;(type-of "newpair (1,true)");pair-type #(struct:int-type) #(struct:bool-type)
;(type-of "- (1,3,true,2)");bad-type
;(type-of "> (false, 9)");bad-type
;(type-of "= (true, ture)");bad-type
;(type-of "if =(1,2) then 5 else false");bad-type
;(type-of "proc(x)x");proc-type (#(struct:tvar-type t0)) #(struct:tvar-type t0))
(type-of "proc(x y) newpair (x,y)")
;(type-of "let f = proc(x) +(x,1) in (f true)");;Wrong