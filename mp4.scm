#lang racket
;partner is sliu19
(require "types-from-staff.scm")
(require eopl)
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



;;Answer = type*subst
;;type-of: Exp*tenv*subst ->answer
(define-datatype answer answer?
  (my-answer
   (type type?)
   (subst substitution?)))

(define answer->type
  (lambda (ans)
    (cases answer ans
      (my-answer(ty sub) ty)
      (else ans))))


(define answer->sub
  (lambda (ans)
    (cases answer ans
      (my-answer(ty sub) sub)
      (else ans))))

;;Add for bad-type check
(define an-answer
  (lambda (type sub)
    (if (substitution? sub)
        (my-answer type sub)
        (my-answer (bad-type) '()))))

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

;;CheckType
;;Notice input shoud be type.
(define typeCheck
  (lambda (ty1 ty2)
    (if (equal? ty1 ty2)
         #t
         #f)))


;;Refered from slides
(define-datatype proc proc?
  (procedure
   (bvar list?)
   (body expression?)
   (env type-environment?)))

;;define environment; code from slides and textbook pg.86 figure 3.12
 ;; why are these separated?

(define-datatype type-environment type-environment?
  (empty-tenv-record)
  (extended-tenv-record
   (sym symbol?)
   (type type?)
   (tenv type-environment?)))

;(define extend-tenv extended-tenv-record)

(define empty-tenv
  (lambda () '()))
 
(define extend-tenv
  (lambda (key value env)
      (cond ((null? env) (list (list key value)))
            ((equal? (caar env) key) (append (list (list key value)) (cdr env)))
            (else (append (list (car env)) (extend-tenv key value (cdr env) ))))))
 
; seek only
(define apply-helper
  (lambda (env key)
    (cond ((null? env) (bad-type))
          ((equal? key (caar env)) (cadar env))
          (else (apply-helper (cdr env) key)))))
 
(define apply-tenv
  (lambda (key env)
  (apply-helper env key)))

(define apply-ttenv 
  (lambda (sym tenv)
    (cases type-environment tenv
      (empty-tenv-record ()
                         (eopl:error 'apply-tenv "Unbound variable ~s" sym))
      (extended-tenv-record (sym1 val1 old-env)
                            (if (eqv? sym sym1) 
                                val1
                                (apply-tenv sym old-env ))))))

(define init-tenv
  (lambda ()
    (extend-tenv 'x (int-type) 
                 (extend-tenv 'v (int-type)
                              (extend-tenv 'i (int-type)
                                           (empty-tenv))))))

;; fresh-tvar-type : () -> Type
;; Page: 265  
(define fresh-tvar-type
  (let ((sn 0))
    (lambda ()
      (set! sn (+ sn 1))
      (tvar-type 'sn))))

;; otype->type : OptionalType -> Type
;; Page: 265
;;deleted 

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


(define tvar-type?
  (lambda (ty)
    (cases type ty
      (tvar-type(sym) #t)
      (else #f))))

(define proc-type?
  (lambda (ty)
    (cases type ty
      (proc-type(t1 t2) #t)
      (else #f))))

(define proc-exp?
  (lambda (ty)
    (cases expression ty
      (proc-exp(t1 t2) #t)
      (else #f))))

(define proc-exp->var-list
  (lambda (exp)
    (cases expression exp
      (proc-exp(exp-list t2) exp-list)
      (else #f))))

(define proc-exp->body
  (lambda (exp)
    (cases expression exp
      (proc-exp(exp-list body) body)
       (else #f))))

(define bad-type?
  (lambda (ty)
    (cond
      [(type? ty)
       (cases type ty
         (bad-type() #t)
         (else #f))]
      (else #f))))

(define proc-type->arg-type
  (lambda (ty)
    (cases type ty
      (proc-type (arg-type result-type) arg-type)
      (else (eopl:error 'proc-type->arg-type
                        "Not a proc type: ~s" ty)))))

(define proc-type->result-type
  (lambda (ty)
    (cases type ty
      (proc-type (arg-type result-type) result-type)
      (else (eopl:error 'proc-type->result-types
                        "Not a proc type: ~s" ty)))))

;; type-to-external-form : Type -> List
;; Page: 266
(define type-to-external-form
  (lambda (ty)
    (cases type ty
      (int-type () 'int)
      (bool-type () 'bool)
      (proc-type (arg-type result-type)
                 (list
                  (type-to-external-form arg-type)
                  '->
                  (type-to-external-form result-type)))
      (tvar-type (serial-number)
                 (string->symbol
                  (string-append
                   "tvar"
                   (if (number? serial-number)
                       (number->string serial-number)
                       (symbol->string serial-number)))))
      (else 'ty))))

;;;;;;;;;;;;;;;; Unit substitution ;;;;;;;;;;;;;;;;

;; apply-one-subst: type * tvar * type -> type
;; (apply-one-subst ty0 var ty1) returns the type obtained by
;; substituting ty1 for every occurrence of tvar in ty0.  This is
;; sometimes written ty0[tvar=ty1]

;; apply-one-subst : Type * Tvar * Type -> Type
;; Page: 260
(define apply-one-subst
  (lambda (ty0 tvar ty1)
    (cases type ty0
      (int-type () (int-type))
      (bool-type () (bool-type))
      (proc-type (arg-type result-type)
                 (proc-type
                  (apply-one-subst arg-type tvar ty1)
                  (apply-one-subst result-type tvar ty1)))
      (tvar-type (sn)
                 (if (equal? ty0 tvar) ty1 ty0))
      (bad-type ty0))))

;;;;;;;;;;;;;;;; Substitutions ;;;;;;;;;;;;;;;;

;; a substitution is a map from unknown types to types.
;; we'll represent this as an association list.

(define pair-of
  (lambda (pred1 pred2)
    (lambda (val)
      (and (pair? val) (pred1 (car val)) (pred2 (cdr val))))))


(define substitution?
  (list-of (pair-of tvar-type? type?)))
;; basic observer: apply-subst-to-type
;; this is sometimes written ty1.subst 

;; apply-subst-to-type : Type * Subst -> Type
;; Page: 261
(define apply-subst-to-type
  (lambda (ty subst)
    (cond
      [(bad-type? subst) (bad-type)]
      [else 
       (cases type ty
         (int-type () (int-type))
         (bool-type () (bool-type))
         (proc-type (t1 t2)
                    (proc-type
                     (many-to-one-map apply-subst-to-type t1 subst)
                     (apply-subst-to-type t2 subst)))
         (tvar-type (sn)
                    (let ((tmp (assoc ty subst)))
                      (if tmp
                          (cdr tmp)
                          ty)))
         (bad-type ty))])))

;; empty-subst : () -> Subst
;; produces a representation of the empty substitution.

;; extend-subst : Subst * Tvar * Type -> Subst

;; (extend-subst s tv t) produces a substitution with the property
;; that for all t0,

;;   (apply-subst t0 (extend-subst s tv t))
;;   = (apply-one-subst (apply-subst t0 s) tv t)

;; i.e.,  t0.(s[tv=t]) = (t0.s)[tv=t]

;; this means that for any type variable tv0 in the domain of s,

;;   (apply-subst tv0 (extend-subst s tv t))
;;   = (apply-one-subst (apply-subst tv0 s) tv t)

;; so we extend the substitution with a new element, and apply [t/v] to every
;; element already in the substitution. 



;; empty-subst : () -> Subst
;; Page 262
(define empty-subst (lambda () '()))

;; extend-subst : Subst * Tvar * Type -> Subst
;; usage: tvar not already bound in subst.
;; Page: 262
(define extend-subst
  (lambda (subst tvar ty)
    (cons
     (cons tvar ty)
     (map 
      (lambda (p)
        (let ((oldlhs (car p))
              (oldrhs (cdr p)))
          (cons
           oldlhs
           (apply-one-subst oldrhs tvar ty))))
      subst))))

;; unifier : Type * Type * Subst * Exp -> Subst OR Fails
;; Page: 264
(define unifier
  (lambda (ty1 ty2 subst exp)
    (let ((ty1 (apply-subst-to-type ty1 subst))
          (ty2 (apply-subst-to-type ty2 subst)))
      (cond
        ((equal? ty1 ty2) subst)            
        ((tvar-type? ty1)
         (if (no-occurrence? ty1 ty2)
             (extend-subst subst ty1 ty2)
             (bad-type)))
        ((tvar-type? ty2)
         (if (no-occurrence? ty2 ty1)
             (extend-subst subst ty2 ty1)
             (bad-type)))
        ((and (proc-type? ty1) (proc-type? ty2))
         (let ((subst (list-unifier
                       (proc-type->arg-type ty1)
                       (proc-type->arg-type ty2)
                       subst exp)))
           (let ((subst (unifier
                         (proc-type->result-type ty1)
                         (proc-type->result-type ty2)
                         subst exp)))
             subst)))
        (else (report-unification-failure))))))


(define report-unification-failure
    bad-type)

(define report-no-occurrence-violation
  (lambda (ty1 ty2 exp)
    (eopl:error 'check-no-occurence!
                "Can't unify: type variable ~s occurs in type ~s in expression ~s~%" 
                (type-to-external-form ty1)
                (type-to-external-form ty2)
                exp)))

;; no-occurrence? : Tvar * Type -> Bool
;; usage: Is there an occurrence of tvar in ty?
;; Page: 265
(define no-occurrence?
  (lambda (tvar ty)
    (cases type ty
      (int-type () #t)
      (bool-type () #t)
      (proc-type (arg-type-list result-type)
                 (and
                  (andBool (many-to-one-map no-occurrence? arg-type-list tvar))
                  (no-occurrence? tvar result-type)))
      (tvar-type (serial-number) (not (equal? tvar ty)))
      (bad-type #f))))




;=====================================type-of-exp========================================
; For proc expression

(define (zip . xss) (apply map list xss))

(define get-args-placeholders
  (lambda (args-list)
    (map tvar-type (map get-var-id args-list))))

(define get-var-id
  (lambda x
    (string->symbol (string-append "t" (number->string (global-counter))))))

(define global-counter
  (let ((count 0))
    (lambda ()
      (set! count (+ count 1))
      count)))

(define filter-id
  (lambda (id-expr-pair id)
    (if (equal? (car id-expr-pair) id)
        '()
        '(id-expr-pair))))

(define mapping-invalidate-key 
  (lambda (mapping target-id)
    (let [(front (car mapping))
          (rest (cdr mapping))]
      (if (null? rest)
          (filter-id front target-id)
          (append (filter-id front target-id) (mapping-invalidate-key rest target-id))))))
(define mapping-invalidate-all-keys 
  (lambda (mapping key-list)
    (if (null? key-list)
        mapping
        (let [(new-mapping (mapping-invalidate-key (car key-list)))]
          (mapping-invalidate-all-keys new-mapping (cdr key-list))))))

; Replace instantiated identifiers : For 1 to n, replace in expr_i, invalidate identifier_i in mapping structure
; Return the modified id-var mapping structure in a tuple : (all replaced exprs, final mapping)
(define let-recursive-replacement
  (lambda (var-exp-pairs id-mappings replaced-exps)
    (if (null? var-exp-pairs)
        (replaced-exps id-mappings)
        (let* [(front (car var-exp-pairs))
              (rest (cdr var-exp-pairs))
              (bind-id (car front))
              (bind-expr (cdr front))
              (new-expr (replace-uninstantiated-vars bind-expr id-mappings))
              (new-mapping (mapping-invalidate-key id-mappings bind-id))]
          (let-recursive-replacement rest new-mapping (append replaced-exps (list new-expr)))))))

(define let-replace
  (lambda (vars exps id-mappings)
    (let* [(var-exp-pairs (zip vars exps))
           (new-exp-mapping (let-recursive-replacement var-exp-pairs id-mappings '()))]
      (vars (car new-exp-mapping) (cadr new-exp-mapping)))))

(define mapping-contains
  (lambda (mapping target)
    (if (null? mapping) 
        #f
        (if (equal? target (caar mapping))
            #t
            (mapping-contains (cdr mapping) target)))))

(define mapping-get
  (lambda (mapping target)
    (if (null? mapping) 
        '()
        (if (equal? target (caar mapping))
            (cadar mapping)
            (mapping-get (cdr mapping) target)))))

(define replace-vars-in-expr-list
  (lambda (expr-list id-mappings)
    (map (lambda (exp) (replace-uninstantiated-vars exp id-mappings)) expr-list)))

(define replace-uninstantiated-vars
  (lambda (expr id-mappings)
    (cases expression expr
      (num-exp (num) expr)
      (true-exp () true-exp)
      (false-exp () false-exp)
      (var-exp (var) 
               (if (mapping-contains id-mappings var)
                   (mapping-get id-mappings var)
                   var-exp))
      (let-exp (var-list exp1-list body)
               (let* [(var-exp-mapping (let-replace var-list exp1-list id-mappings))
                      (new-exp-list (cadr var-exp-mapping))
                      (new-mapping (caddr var-exp-mapping))
                      (replaced-body (replace-uninstantiated-vars body new-mapping))]
                 (let-exp var-list new-exp-list replaced-body)))
      
      ; Letrec is different - invalidate all keys in the mapping which correspond to var-list identifiers
      (letrec-exp (var-list exp-list body)
                  (let* [(new-mapping (mapping-invalidate-all-keys id-mappings var-list))
                         (new-expr-list (replace-vars-in-expr-list exp-list id-mappings))
                         (new-body (replace-uninstantiated-vars body new-mapping))]
                    (letrec-exp var-list new-expr-list new-body)))
      
      (proc-exp (var-list exp)
                (let [(new-mapping (mapping-invalidate-all-keys id-mappings var-list))]
                  (proc-exp var-list (replace-uninstantiated-vars exp new-mapping))))
      (exp-exp (rator rand-list)
               (let* [(new-rator (replace-uninstantiated-vars rator id-mappings))
                      (new-rands (replace-vars-in-expr-list rand-list id-mappings))]
                 (exp-exp new-rator new-rands)))
      (begin-exp (exp1 exp2-list)
                 (let* [(new-exp1 (replace-uninstantiated-vars exp1 id-mappings))
                        (new-exp2-list (replace-vars-in-expr-list exp2-list id-mappings))]
                 (begin-exp new-exp1 new-exp2-list)))
      (if-exp (e1 e2 e3)
              (let* [(new-e1 (replace-uninstantiated-vars e1 id-mappings))
                     (new-e2 (replace-uninstantiated-vars e2 id-mappings))
                     (new-e3 (replace-uninstantiated-vars e3 id-mappings))]
                (if-exp new-e1 new-e2 new-e3)))
      (arith-exp (op e1 e2)
                 (let* [(new-e1 (replace-uninstantiated-vars e1 id-mappings))
                        (new-e2 (replace-uninstantiated-vars e2 id-mappings))]
                   (arith-exp op new-e1 new-e2)))
      (compare-exp (op e1 e2)
                (let* [(new-e1 (replace-uninstantiated-vars e1 id-mappings))
                     (new-e2 (replace-uninstantiated-vars e2 id-mappings))]
                (compare-exp op new-e1 new-e2)))
      (compare-equ-exp (e1 e2)
                (let* [(new-e1 (replace-uninstantiated-vars e1 id-mappings))
                     (new-e2 (replace-uninstantiated-vars e2 id-mappings))]
                (compare-equ-exp new-e1 new-e2)))
      (newpair-exp (e1 e2) 
                   (let* [(new-e1 (replace-uninstantiated-vars e1 id-mappings))
                          (new-e2 (replace-uninstantiated-vars e2 id-mappings))]
                     (newpair-exp new-e1 new-e2)))
      
      (first-exp (e1) 
                (let [(new-e1 (replace-uninstantiated-vars e1 id-mappings))]
                  (first-exp new-e1)))
      (second-exp (e1) 
                (let [(new-e1 (replace-uninstantiated-vars e1 id-mappings))]
                  (second-exp new-e1)))
      
      )))

(define get-proc-arg-identifiers
  (lambda (expr-type)
    (if (expression? proc-exp) 
        (cases expression exp
          (proc-exp (var-list body-exp) var-list)
          (else '()))
        '())))

(define extend-multi-env
  (lambda (env pairs)
    (if (null? pairs)
        env
        (let* [(first-pair (car pairs))
               (identifier (car first-pair))
               (value (cadr first-pair))
               (remaining (cdr pairs))]
          (if (answer? value)
              (cases answer value
                (my-answer (type subst) 
                           (extend-multi-env (extend-tenv type value env) remaining)))
              (extend-multi-env (extend-tenv identifier value env) remaining))))))

(define list-index-of
  (lambda (lst idx)
    (if (equal? 0 idx)
        (car lst)
        (list-index-of (cdr lst) (- idx 1)))))

(define match-tvar
  (lambda (var-list target-id idx)
    (if (null? var-list)
        -1
        (let [(t1 (car var-list))]
          (cases type t1
            (tvar-type (id-number)
                       (if (equal? id-number target-id)
                           idx
                           (match-tvar (cdr var-list) target-id (+ 1 idx))))
            (else (match-tvar (cdr var-list target-id (+ 1 idx)))))))))

(define poly-tvar-resolve
  (lambda (tvar args-id-list type-list subst)
    (cases type tvar
      (tvar-type (tvar-id) (poly-type-resolve args-id-list type-list tvar-id tvar subst))
      (else (bad-type)))))

(define poly-type-resolve
  (lambda (args-id-list type-list tvar-id tval-type subst)
    (let [(args-idx (match-tvar args-id-list tvar-id 0))]
      (if (equal? -1 args-idx)
          (my-answer tval-type subst) ; Cannot find type
          (begin (list-index-of type-list args-idx))))))

(define extract-from-answer
  (lambda (var)
    (if (answer? var)
        (answer->type var)
        var)))

(define consistent-type-args
  (lambda (proc-type-list given-type-list)
    (cond ((and (null? proc-type-list) (null? given-type-list)) #t)
          ((or (null? proc-type-list) (null? given-type-list)) #f) 
          (else 
           ;; This is the general case 
           (let [(t1 (extract-from-answer (car proc-type-list)))
                 (t2 (extract-from-answer (car given-type-list)))]
             (if (equal? (length proc-type-list) (length given-type-list))
                 (if (null? proc-type-list)
                     #t
                     (cases type t1
                       (tvar-type (serial) (consistent-type-args (cdr proc-type-list) (cdr given-type-list)))
                       (else (if (equal? t1 t2)
                                 (consistent-type-args (cdr proc-type-list) (cdr given-type-list))
                                 #f))))
                 #f))))))
  
                           

(define type-of-exp
  (lambda (exp env subst args-continuation)
    (cond 
      [(type? exp) (an-answer exp subst)]
      [(answer? exp) exp]
      [else 
    (cases expression exp
      (num-exp (number) (an-answer (int-type) subst))
      
      (var-exp (var) (an-answer (apply-tenv var env) subst))
      
      (true-exp () (an-answer (bool-type) subst))
      
      (false-exp () (an-answer (bool-type) subst))
      
      (let-exp (var-list exp1-list exp2)
               (type-of-exp exp2
                        (add-env var-list exp1-list env subst) subst '()))
      
      (letrec-exp (var-list exp1-list body)
                 (let* [(new-env (add-env-letrec var-list exp1-list env subst))
                        (new-env (resolve-letrec var-list new-env subst))
                        (new-subst (resolve-letrec-sub var-list new-env subst))
                        ;(write '444444444)
                        (ans (type-of-exp body new-env new-subst '()))]
                  ; (write '33333333333333333333)
                   (an-answer (apply-subst-to-type (answer->type ans) (answer->sub ans)) new-subst)))
                 
      (proc-exp (var-list exp)
                (let*[(var-list-type (getNewTvar var-list subst))
                      (env (add-env var-list var-list-type env subst))]
                  (if (equal? (length var-list) (length args-continuation))
                      ; Called from apply-expression
                      (let* [(new-type-mappings (zip var-list args-continuation))
                             (new-type-env (add-env var-list args-continuation env subst))]
                        (cases answer (type-of-exp exp new-type-env subst '())
                          (my-answer (result-type subst)
                                     (an-answer (proc-type (get-arg-type-list var-list-type subst) result-type) subst))))
                      
                      (cases answer (type-of-exp exp env subst '())
                        (my-answer (result-type subst)
                                   (an-answer 
                                    (proc-type (get-arg-type-list var-list-type subst) result-type) 
                                    subst))))))
      ;(proc-exp (var-list exp)
      ;          (let*[(var-list-type (getNewTvar var-list subst))
      ;            (env (add-env var-list var-list-type env subst))]
      ;           
      ;        (cases answer (type-of-exp exp env subst)
      ;            (my-answer (result-type subst)
      ;                       (an-answer
      ;                        (proc-type (get-arg-type-list var-list-type subst) result-type)
      ;                        subst)))))
     ; 
    ; (proc-exp (var-list exp)
     ;           (let* [(var-types (get-args-placeholders var-list))
      ;                (identifier-var-mapping (zip var-list var-types))]
       ;           (proc-type var-types (type-of-exp (replace-uninstantiated-vars exp identifier-var-mapping) env))))
      
      ;;Notice I am not sure how to deal with rand-list insteat of rand, I put car at line 586 for now.
      (exp-exp (rator rand-list)
               ;(let ((result-type (fresh-tvar-type)))
               ;  (cases answer (type-of-exp rator env subst)
               ;    (my-answer (rator-type subst)
               ;               (cases answer (type-of-exp (car rand-list) env subst)
               ;                 (my-answer (rand-type subst)
               ;                            (let ((subst
               ;                                   (unifier rator-type
               ;                                            (proc-type (list rand-type) result-type)
               ;                                            subst
               ;                                            exp)))
               ;                              (an-answer (apply-subst-to-type result-type subst) subst))))))))
               
               ;; One complexity is because operator expression is not guaranteed to be proc-expression 
               (let* [(arg-types (map (lambda (exp) (type-of-exp exp env subst '())) rand-list))]
                 (cases answer (type-of-exp rator env subst rand-list) ; Reduce operator expression to proc type
                   (my-answer (rator-proc subst)
                              ; Assert the rator is a proc (otherwise bad type) and evaluate the result-type
                              (if (type? rator-proc)
                                  (cases type rator-proc
                                    (proc-type (arg-list result-type) 
                                               ; Polymorphism of result type
                                               (cases type result-type
                                                 ; If same tvar is present in args list, we can perform substitution
                                                 ; Dont need to check type consistency for t-var becuase inference doesnt know anything.
                                                 (tvar-type (tvar-id) 
                                                            (begin
                                                            (poly-type-resolve arg-list arg-types tvar-id result-type subst)))
                                                 (pair-type (p1 p2)
                                                            (let [(p1-type (cases type p1
                                                                             (tvar-type (id) (answer->type (poly-tvar-resolve p1 arg-list arg-types subst)))
                                                                             (else p1)))
                                                                  (p2-type (cases type p2 
                                                                             (tvar-type (id) (answer->type (poly-tvar-resolve p2 arg-list arg-types subst)))
                                                                             (else p2)))]
                                                              (my-answer (pair-type p1-type p2-type) subst)))
                                                             
                                                 ; Make this consistent
                                                 (else (if (consistent-type-args arg-list arg-types) 
                                                           (my-answer result-type subst)
                                                           (my-answer (bad-type) subst)))))
                                    (else (my-answer (bad-type) subst)))
                                  (my-answer (bad-type) subst))))))
      
      ;(begin-exp (exp1 exp2-list) (type-of-exp-begin exp1 exp2-list env state));;TO DO
      ; 1) Begin returns the value of the last expression, so we return type-of last expression
      ; 2) None of the language expressions can modify the environment 
      ;    (since we are not using store and environment bindings from let only appy to the let-body)
      ; So, we can return type-of last expression with the input environment 
      (begin-exp (exp1 exp2-list) 
                (let [(ans (type-of-exp exp1 env subst '()))]
                 (if (null? exp2-list)
                     (apply-subst-to-type (answer->type ans) (answer->sub ans))
                     (begin-list (append (list exp1) exp2-list) env subst))))
      
      (if-exp(exp1 exp2 exp3)
             (cases answer (type-of-exp exp1 env subst '())
               (my-answer (ty1 subst1)
                          
                          (let ((subst (unifier ty1 (bool-type) subst
                                                exp1)))
                            (cases answer (type-of-exp exp2 env subst '())
                              (my-answer (ty2 subst)
                                         (cases answer (type-of-exp exp3 env subst '())
                                           (my-answer (ty3 subst)
                                                      (let ((subst (unifier ty2 ty3 subst exp)))
                                                        (an-answer ty3 subst))))))))))
               
               ;(my-answer (ty1 subst1)
               ;           (let ((subst (unifier ty1 (bool-type) subst
               ;                                 exp1)))
               ;             (cases answer (type-of-exp exp2 env subst '())
               ;               (my-answer (ty2 subst)
               ;                          (cases answer (type-of-exp exp3 env subst '())
               ;                            (my-answer (ty3 subst)
               ;                                       (let ((subst (unifier ty2 ty3 subst exp)))
               ;                                         (an-answer ty2 subst))))))))))
      
      
      ;;For now only consider first elemnt of exp2
      (arith-exp(arith-op exp1 exp2)
                (let* [(ty1 (answer->type (type-of-exp exp1 env subst '())))
                      (ty2-list ( map answer->type (many-to-one-to-one-map type-of-exp exp2 env subst '())))
                      (subst (unifier ty1 (int-type) subst exp1))
                      (subst (list-unifier ty2-list (replicate (int-type) (length ty2-list))subst exp2))]
                   (an-answer (apply-subst-to-type ty1 subst)subst)))
      
      (compare-exp(compare-op exp1 exp2)
                  (let* [(ty1 (answer->type (type-of-exp exp1 env subst '())))
                         (ty2 (answer->type (type-of-exp exp2 env subst '())))
                         (subst (unifier ty1 ty2 subst exp1))]
                    (an-answer (bool-type) subst)))
      
      (compare-equ-exp(exp1 exp2)
                      (let* [(ty1 (answer->type (type-of-exp exp1 env subst '())))
                             (ty2 (answer->type (type-of-exp exp2 env subst '())))
                             (subst (unifier ty1 ty2 subst exp1))]
                        (an-answer (bool-type) subst)))
      
      (newpair-exp (exp1 exp2) 
                   (let [(ty1 (type-of-exp exp1 env subst '()))
                         (ty2 (type-of-exp exp2 env subst '()))]
                     (an-answer (pair-type (answer->type ty1) (answer->type ty2)) subst)))
      
      (first-exp(exp) 
                (let [(ty1 (answer->type (type-of-exp exp env subst '())))]
                 (cases type ty1
                   (pair-type(first second) (an-answer first subst))
                   (else (an-answer (bad-type) subst)))))
      
      (second-exp (exp)  
                    (let [(ty1 (answer->type (type-of-exp exp env subst '())))]
                 (cases type ty1
                   (pair-type(first second) (an-answer second subst))
                   (else (an-answer (bad-type) subst)))))
      
      (else exp))])))


(define andBool
  (lambda (exp-list)
    (if (null? (cdr exp-list))
        (cdr exp-list)
        (and (car exp-list) (andBool (cdr exp-list))))))

(define getNewTvar
  (lambda (var-list subst)
   (map (lambda (list) (tvar-type (gensym)))  var-list)))


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


(define add-env
  (lambda (var-list exp1-list env subst)
    (if (or (null? var-list) (null? exp1-list))
        env
        (let ([newtype (answer->type (type-of-exp (car exp1-list) env subst '()) )])
          (if (null? (cdr var-list)) 
              (extend-tenv (car var-list) newtype env)
              (add-env (cdr var-list) (cdr exp1-list) (extend-tenv (car var-list) newtype env) subst))))))

(define add-env-letrec
  (lambda (var-list exp1-list env subst)
    ;;(let [(ty (answer->type (type-of-exp (car exp1-list) env subst)))]
    (if (null? (cdr var-list))
        (cond
          [(proc-exp? (car exp1-list))
                    (let [(var (getNewTvar (proc-exp->var-list (car exp1-list) ) subst))
                          (result (tvar-type (gensym)))]
                     (extend-tenv (string->symbol (string-append (symbol->string (car var-list)) "1")) (car exp1-list) (extend-tenv (car var-list) (proc-type var result) env)))]
          ;;exp-list is not proc
          (else (extend-tenv (car var-list) (answer->type (type-of-exp (car exp1-list) env subst '())) env)))
        (cond
          [(proc-exp? (car exp1-list))
                    (let [(var (getNewTvar (proc-exp->var-list (car exp1-list)) subst))
                          (result (tvar-type (gensym)))]
                    (add-env-letrec (cdr var-list) (cdr exp1-list)(extend-tenv (string->symbol (string-append (symbol->string (car var-list)) "1")) (car exp1-list) (extend-tenv (car var-list) (proc-type var result) env) ) subst))]
          (else (add-env-letrec (cdr var-list) (cdr exp1-list) (extend-tenv (car var-list)  (answer->type (type-of-exp (car exp1-list) env subst)) env) subst ))))))


(define resolve-letrec
  (lambda (var-list env subst)
    (let ([newtype  (apply-subst-to-type(answer->type(type-of-exp (apply-tenv (string->symbol (string-append (symbol->string (car var-list)) "1")) env) env subst '()))subst)])
      (if (null? (cdr var-list)) 
          (extend-tenv (car var-list) newtype env)
          (resolve-letrec (cdr var-list) (extend-tenv (car var-list) newtype env) subst)))))

(define resolve-letrec-sub
  (lambda (var-list env subst)
    (let ([newsub (answer->sub (type-of-exp (apply-tenv (string->symbol (string-append (symbol->string (car var-list)) "1")) env) env subst '()))]
          [newtype  (apply-subst-to-type(answer->type(type-of-exp (apply-tenv (string->symbol (string-append (symbol->string (car var-list)) "1")) env) env subst '()))subst)])
      (if (null? (cdr var-list)) 
          (cond 
            [(null? newsub) subst]
            [else newsub])
            ;[else (write '11) (extend-subst (car subst) (car newsub) (cdr newsub))])
          (cond
            [(null? newsub) (resolve-letrec-sub (cdr var-list) (extend-tenv (car var-list) newtype env) subst)]
            [(null? subst) (resolve-letrec-sub (cdr var-list) (extend-tenv (car var-list) newtype env) newsub)]
            [else (extend-subst (resolve-letrec-sub (cdr var-list) (extend-tenv (car var-list) newtype env) subst) (car newsub) (cdr newsub) )])))))

   


(define get-arg-type-list
  (lambda (arg-list subst)
    (let* [(list-length  (length arg-list))
           (sub-list (replicate subst list-length))]
           (map apply-subst-to-type arg-list sub-list))))

(define many-to-one-map
  (lambda (map-func exp1-list exp2) 
    (let [(exp2-list (replicate exp2 (length exp1-list)))]
      (map map-func exp1-list exp2-list))))

(define many-to-one-to-one-map
  (lambda (map-func exp1-list exp2 exp3 exp4) 
    (let [(exp2-list (replicate exp2 (length exp1-list)))
          (exp3-list (replicate exp3 (length exp1-list)))
          (exp4-list (replicate exp4 (length exp1-list)))]
      (map map-func exp1-list exp2-list exp3-list exp4-list))))

(define list-unifier
  (lambda (ty1-list ty2-list subst exp)
    (if (or (null? ty1-list) (null? ty2-list))
        '()
        (if (null?(cdr ty1-list))
            (unifier (car ty1-list) (car ty2-list) subst exp)
            (list-unifier (cdr ty1-list) (cdr ty2-list) (unifier (car ty1-list) (car ty2-list) subst exp) exp)))))
  
(define begin-list
  (lambda (arg-list env subst)
    (let [(ans (type-of-exp (car arg-list) env subst '()))]
      (if(null? (cdr arg-list))
         (apply-subst-to-type (answer->type ans) (answer->sub ans))
         (cond
           [(bad-type? (answer->type (type-of-exp (car arg-list) env subst '()))) (my-answer (bad-type) subst)]
           [else (begin-list (cdr arg-list) env (answer->sub (type-of-exp (car arg-list) env subst '())))])))))
  
  
  (define add-env-proc
    (lambda (var-list exp1-list env state)
      (if (null? (cdr var-list))
          (cond 
            [(expression? (car exp1-list)) 
             (extend-tenv (car var-list) (type-of-exp (car exp1-list) env state '()) env)]
            [else (extend-tenv (car var-list) (type-of-exp(car exp1-list) env state '()) env)])
          (cond 
            [(expression? (car exp1-list)) 
             (extend-tenv (car var-list) (type-of-exp (car exp1-list) env state '()) (add-env-proc (cdr var-list) (cdr exp1-list) env state))]
            [else (extend-tenv (car var-list) (type-of-exp (car exp1-list) env state '()) (add-env-proc (cdr var-list) (cdr exp1-list) env state))]))))
  
  ;;================Two cases to resolve letrec and curry==============
  (define apply-procedure
    (lambda (proc1 arg state)
    (cases proc proc1
      (procedure (var body saved-env)
                 (let ((new-env (add-env-proc var arg saved-env state)))
                   (type-of-exp body new-env state '()))))))



;==============================Wrap Func=================================
(define type-of
  (lambda (exp)
    (let [(result (type-of-exp (scan&parse exp) (empty-tenv) (empty-subst) '()))]
      (if (answer? result)
          (answer->type result)
          result))))

;=====================================Test========================================


;;; Unit test
(define (reportmsg msg)
	(display msg)
	(newline))
 (define (reporterr msg)
	(display "ERROR: ")
	(display msg)
	(newline))
(define (assert msg b)
  (if (not b) (reporterr msg) b))
(define (asserteq msg a b) (assert msg (equal? a b)))

; Primitives - Not testing for unbound identifier
;(asserteq "test1" (type-of "1") (int-type))
;(asserteq "test2" (type-of "false") (bool-type))
;(asserteq "test3" (type-of "true") (bool-type))

; First, Second
;(asserteq "test4" (type-of "let x = newpair (1,2) in first (x)") (int-type))
;(asserteq "test5" (type-of "let x = newpair (1,true) in second (x)") (bool-type))

; NewPair
;(asserteq "test6" (type-of "newpair (1,true)") (pair-type (int-type) (bool-type)))
;(asserteq "test7" (type-of "newpair (false,true)") (pair-type (bool-type) (bool-type)))
;(asserteq "test8" (type-of "newpair (1, 2)") (pair-type (int-type) (int-type)))

; Comparison, Arithmetic. Only allows integer operands.
;(asserteq "test9" (type-of "=(1,2)") (bool-type))
;(asserteq "test10" (type-of "=(1,true)") (bad-type))
;(asserteq "test11" (type-of "+(1,2)") (int-type))
;(asserteq "test12" (type-of "+(1,true)") (bad-type))
;(asserteq "test13" (type-of "-(1,2)") (int-type))
;(asserteq "test14" (type-of "-(1,true)") (bad-type))

; IF : bad type if the last two expressions are not the same type 
;(asserteq "test15" (type-of "if =(1, 2) then 5 else false") (bad-type))
;(asserteq "test16" (type-of "if =(1, 2) then 5 else 4") (int-type))

;;PASSED:
;(type-of "let f = proc (x) +(x,1) in (f 2)");int-type
;(type-of "- (1,3,true,2)");bad-type
;(type-of "> (false, 9)");bad-type
;(type-of "= (true, ture)");bad-type
;(type-of "if =(1,2) then 5 else false");bad-type
;(type-of "proc(x)x");proc-type (#(struct:tvar-type t0)) #(struct:tvar-type t0))
;(type-of "proc(x y) newpair (x,y)")
;(type-of "proc(x)x");(proc-type (list (tvar-type 'g210790)) (tvar-type 'g210790))
;(type-of "proc(x) +(x,1)")
;(type-of "let f = proc(x) +(x,1) in (f true)");bad-type
;(type-of "let f = proc(x) +(x,1) in (f 2)");int-type
;(type-of "let f = proc(x) x in if (f true) then (f 3) else (f 5)");int-type
;(type-of "let f = proc(x) x in newpair((f true),(f 8))");(pair-type (bool-type) (int-type))
;(type-of "proc (x) +(x,1)");(proc-type (list (int-type)) (int-type))

;(type-of "begin if 5 then 5 else 7; 5 end");bad type
;(type-of "begin if =(1,2) then 5 else 7; 5 end");int type
;(type-of "begin if =(1,2) then 5 else 7; true end");bool type

;(type-of "(proc(y) if (y true) then (y 4) else 0 proc (x) x)")
;(type-of "(proc(y) if (y true) then (y 4) else 0 proc (x) x)")
;(type-of "proc(y) if (y true) then (y 4) else 0")

;;Letrec
;(type-of "letrec ill = proc(x) (ill x) in (ill 5)")
;
(provide type-of)