#lang eopl

(define-datatype type type?
  (int-type)
  (bool-type)
  (proc-type
   (arg-types (list-of type?))
   (return-type type?))
  (pair-type
   (first-type type?)
   (second-type type?))
  (tvar-type
   (sym symbol?))
  (bad-type))

(provide type type? int-type bool-type proc-type bad-type pair-type tvar-type)
