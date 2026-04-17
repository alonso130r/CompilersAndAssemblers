#lang racket
;; chinmay jindal 

(define (bin->parts x)
  (match x
    [(add l r) (list 'add l r)]
    [(sub l r) (list 'sub l r)]
    [(mul l r) (list 'mul l r)]
    [(div l r) (list 'div l r)]
    [(mod l r) (list 'mod l r)]
    [(equal l r) (list 'equal l r)]
    [(gt l r) (list 'gt l r)]
    [(lt l r) (list 'lt l r)]
    [(ge l r) (list 'ge l r)]
    [(le l r) (list 'le l r)]
    [x #f]))

(define-match-expander bin/op
  (syntax-rules ()
    [(_ op lhs rhs)
     (app bin->parts (list op lhs rhs))]))

;; label counter
(define labcount 0)

;; stmt
(struct print-a (aexp))
(struct print-s (str))
(struct set (id aexp))
(struct seq (stmts))
(struct iif (bexp stmt1 stmt2))
(struct skip ())
(struct while (bexp stmts))

;; aexp
(struct add (aexp1 aexp2))
(struct sub (aexp1 aexp2))
(struct mul (aexp1 aexp2))
(struct div (aexp1 aexp2))
(struct mod (aexp1 aexp2))

(define (aexp? sexp)
  (or (add? sexp) (sub? sexp) (mul? sexp) (div? sexp) (mod? sexp)))

;; bexp
(struct equal (aexp1 aexp2))
(struct gt (aexp1 aexp2))
(struct lt (aexp1 aexp2))
(struct ge (aexp1 aexp2))
(struct le (aexp1 aexp2))
(struct snot (bexp))
(struct sand (bexps))
(struct sor (bexps))

(define (comp? sexp)
  (or (equal? sexp) (gt? sexp) (lt? sexp) (ge? sexp) (le? sexp)))

;; for finding stack max
(define (bin? sexp)
  (or (aexp? sexp) (comp? sexp)))

;; parse result struct
(struct parse-res (var-hash ins-lst))

(define (parse-one stmt)
  (match stmt
    [`(print ,sexp) (define parsed (parse-one sexp))
                    (if (string? parsed)
                        (print-s parsed)
                        (print-a parsed))]
    [`(set ,id ,aexp) (set (string->symbol (string-append "_" (symbol->string id))) (parse-one aexp))]
    [`(seq ,stmts ...) (seq (map parse-one stmts))]
    [`(iif ,bexp ,stmt1 ,stmt2) (iif (parse-one bexp) (parse-one stmt1) (parse-one stmt2))]
    [`(skip) (skip)]
    [`(while ,bexp ,stmts ...) (while (parse-one bexp) (map parse-one stmts))]
    [`(+ ,aexp1 ,aexp2) (add (parse-one aexp1) (parse-one aexp2))]
    [`(- ,aexp1 ,aexp2) (sub (parse-one aexp1) (parse-one aexp2))]
    [`(* ,aexp1 ,aexp2) (mul (parse-one aexp1) (parse-one aexp2))]
    [`(div ,aexp1 ,aexp2) (div (parse-one aexp1) (parse-one aexp2))]
    [`(mod ,aexp1 ,aexp2) (mod (parse-one aexp1) (parse-one aexp2))]
    [`(= ,aexp1 ,aexp2) (equal (parse-one aexp1) (parse-one aexp2))]
    [`(> ,aexp1 ,aexp2) (gt (parse-one aexp1) (parse-one aexp2))]
    [`(< ,aexp1 ,aexp2) (lt (parse-one aexp1) (parse-one aexp2))]
    [`(>= ,aexp1 ,aexp2) (ge (parse-one aexp1) (parse-one aexp2))]
    [`(<= ,aexp1 ,aexp2) (le (parse-one aexp1) (parse-one aexp2))]
    [`(not ,bexp) (snot (parse-one bexp))]
    [`(and ,bexps ...) (sand (map parse-one bexps))]
    [`(or ,bexps ...) (sor (map parse-one bexps))]
    [(? symbol? id) (string->symbol (string-append "_" (symbol->string id)))]
    [x x]))

(define (find-max-stack ast)
  (match ast
    [(bin/op op stmt1 stmt2) (max (find-max-stack stmt1) (add1 (find-max-stack stmt2)))]
    [(print-a aexp) (find-max-stack aexp)]
    [(print-s str) 0]
    [(set x aexp) (find-max-stack aexp)]
    [(seq stmts) (apply max (map find-max-stack stmts))]
    [(iif bexp stmt1 stmt2) (max (find-max-stack bexp) (add1 (find-max-stack stmt1)) (add1 (find-max-stack stmt2)))]
    [(skip) 0]
    [(while bexp stmts) (apply max (map add1 (map find-max-stack (cons bexp stmts))))]
    [(snot bexp) (find-max-stack bexp)]
    [(sor bexps) (if (empty? bexps) 1 (apply max (map find-max-stack bexps)))]
    [(sand bexps) (if (empty? bexps) 1 (apply max (map (λ (x) (max x 2)) (map find-max-stack bexps))))]
    [x 1]))
  

(define (parse code)
  (match-define `(vars [(,ids ,nums) ...] ,stmts ...) code)
  (define vars (make-hash))
  (for ([id ids] [num nums])
    (hash-set! vars (string->symbol (string-append "_" (symbol->string id))) num))
  (parse-res vars (map parse-one stmts)))

(define (compile-one stmt)
  (match stmt
    [(print-a aexp) (append (compile-one aexp)
                            (list `(print-val (-1 sp)))
                            (list `(sub sp sp 1)))]
    [(print-s str) (list `(print-string ,str))]
    [(set id aexp) (append (compile-one aexp)
                           (list `(move ,id (-1 sp))
                                 `(sub sp sp 1)))]
    [(seq stmts) (append-map compile-one stmts)]
    [(iif bexp stmt1 stmt2) (define lab1 (string->symbol (format "LABEL~a" labcount)))
                            (define lab2 (string->symbol (format "LABEL~a" (+ 1 labcount))))
                            (define lab3 (string->symbol (format "LABEL~a" (+ 2 labcount))))
                            (set! labcount (+ labcount 3))
                            (define temp (append (compile-one bexp)
                                                 (list `(branch (-1 sp) ,lab1)
                                                       `(jump ,lab2)
                                                       `(label ,lab1))
                                                 (compile-one stmt1)
                                                 (list `(jump ,lab3)
                                                       `(label ,lab2))
                                                 (compile-one stmt2)
                                                 (list `(label ,lab3)
                                                       `(sub sp sp 1))))
                            temp]
    [(skip) empty]
    [(while bexp stmts) (define lab1 (string->symbol (format "LABEL~a" labcount)))
                        (define lab2 (string->symbol (format "LABEL~a" (+ 1 labcount))))
                        (define lab3 (string->symbol (format "LABEL~a" (+ 2 labcount))))
                        (set! labcount (+ labcount 3))
                        (define temp (append (list `(label ,lab1))
                                             (compile-one bexp)
                                             (list `(branch (-1 sp) ,lab2)
                                                   `(jump ,lab3)
                                                   `(label ,lab2))
                                             (append-map compile-one stmts)
                                             (list `(sub sp sp 1))
                                             (list `(jump ,lab1)
                                                   `(label ,lab3)
                                                   `(sub sp sp 1))))
                        temp]
    [(bin/op op aexp1 aexp2) (append (compile-one aexp1)
                                       (compile-one aexp2)
                                       (list `(,op (-2 sp) (-2 sp) (-1 sp))
                                             `(sub sp sp 1)))]
    [(snot bexp) (append (compile-one bexp)
                         (list `(lnot (-1 sp) (-1 sp))))]
    [(sand bexps) (cond
                    [(empty? bexps) (list `(move (0 sp) ,#t)
                                          `(add sp sp 1))]
                    [else (define lab-short (string->symbol (format "LABEL~a" labcount)))
                          (define lab-end (string->symbol (format "LABEL~a" (+ labcount 1))))
                          (set! labcount (+ labcount 2))
                          (define init-bexps (drop-right bexps 1))
                          (define last-bexp (last bexps))
                          (append (append-map (λ (x)
                                                (append (compile-one x)
                                                        (list `(lnot (0 sp) (-1 sp))
                                                              `(add sp sp 1)
                                                              `(branch (-1 sp) ,lab-short)
                                                              `(sub sp sp 2))))
                                              init-bexps)
                                  (compile-one last-bexp)
                                  (list `(jump ,lab-end)
                                        `(label ,lab-short)
                                        `(sub sp sp 1)
                                        `(label ,lab-end)))])]
    [(sor bexps) (cond
                   [(empty? bexps) (list `(move (0 sp) ,#f)
                                         `(add sp sp 1))]
                   [else (define lab1 (string->symbol (format "LABEL~a" labcount)))
                         (set! labcount (add1 labcount))
                         (define init-bexps (drop-right bexps 1))
                         (define last-bexp (last bexps))
                         (define temp (append (append-map (λ (x)
                                                            (append (compile-one x)
                                                                    (list `(branch (-1 sp) ,lab1)
                                                                          `(sub sp sp 1))))
                                                          init-bexps)
                                              (compile-one last-bexp)
                                              (list `(label ,lab1))))
                         temp])]
    [x (list `(move (0 sp) ,x)
             `(add sp sp 1))]))
  
(define (compile-simpl code)
  (set! labcount 0)
  (define stor (parse code))
  (define vars (parse-res-var-hash stor))
  (define stmts (parse-res-ins-lst stor))
  (define tstack-height (apply max (map find-max-stack stmts)))
  (append (append-map compile-one stmts)
          (map (λ (x) `(data ,(car x) ,(cdr x)))
               (hash->list vars))
          (list `(data stck (,tstack-height 0))
                `(data sp stck))))
  
  