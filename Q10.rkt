#lang racket
;; chinmay jindal

(provide compile-simpl)

(define (bin->parts x)
  (match x
    [(add l r) (list 'add l r)]
    [(sub l r) (list 'sub l r)]
    [(mul l r) (list 'mul l r)]
    [(div l r) (list 'div l r)]
    [(mod l r) (list 'mod l r)]
    [(equ l r) (list 'equal l r)]
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

;; functions
(struct fn (nm ids bdy))
(struct fn-call (nm ids))
(struct return (aexp))

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

;; bexp
(struct equ (aexp1 aexp2))
(struct gt (aexp1 aexp2))
(struct lt (aexp1 aexp2))
(struct ge (aexp1 aexp2))
(struct le (aexp1 aexp2))
(struct snot (bexp))
(struct sand (bexps))
(struct sor (bexps))

;; parse result struct
(struct parse-res (var-hash ins-lst))

(define (parse-one stmt fn-name-hash)
  (match stmt
    [`(print ,sexp) (define parsed (parse-one sexp fn-name-hash))
                (if (string? parsed)
                    (print-s parsed)
                    (print-a parsed))]
    [`(set ,id ,aexp) (set id (parse-one aexp fn-name-hash))]
    [`(seq ,stmts ...) (seq (map (λ (s) (parse-one s fn-name-hash)) stmts))]
    [`(iif ,bexp ,stmt1 ,stmt2) (iif (parse-one bexp fn-name-hash)
                                     (parse-one stmt1 fn-name-hash)
                                     (parse-one stmt2 fn-name-hash))]
    [`(while ,bexp ,stmts ...) (while (parse-one bexp fn-name-hash)
                                      (map (λ (s) (parse-one s fn-name-hash)) stmts))]
    [`(+ ,aexp1 ,aexp2) (add (parse-one aexp1 fn-name-hash) (parse-one aexp2 fn-name-hash))]
    [`(- ,aexp1 ,aexp2) (sub (parse-one aexp1 fn-name-hash) (parse-one aexp2 fn-name-hash))]
    [`(* ,aexp1 ,aexp2) (mul (parse-one aexp1 fn-name-hash) (parse-one aexp2 fn-name-hash))]
    [`(div ,aexp1 ,aexp2) (div (parse-one aexp1 fn-name-hash) (parse-one aexp2 fn-name-hash))]
    [`(mod ,aexp1 ,aexp2) (mod (parse-one aexp1 fn-name-hash) (parse-one aexp2 fn-name-hash))]
    [`(= ,aexp1 ,aexp2) (equ (parse-one aexp1 fn-name-hash) (parse-one aexp2 fn-name-hash))]
    [`(> ,aexp1 ,aexp2) (gt (parse-one aexp1 fn-name-hash) (parse-one aexp2 fn-name-hash))]
    [`(< ,aexp1 ,aexp2) (lt (parse-one aexp1 fn-name-hash) (parse-one aexp2 fn-name-hash))]
    [`(>= ,aexp1 ,aexp2) (ge (parse-one aexp1 fn-name-hash) (parse-one aexp2 fn-name-hash))]
    [`(<= ,aexp1 ,aexp2) (le (parse-one aexp1 fn-name-hash) (parse-one aexp2 fn-name-hash))]
    [`(not ,bexp) (snot (parse-one bexp fn-name-hash))]
    [`(and ,bexps ...) (sand (map (λ (s) (parse-one s fn-name-hash)) bexps))]
    [`(or ,bexps ...) (sor (map (λ (s) (parse-one s fn-name-hash)) bexps))]
    [`(,(? (λ (x) (hash-has-key? fn-name-hash x)) nm) ,ids ...)
     (fn-call nm (map (λ (s) (parse-one s fn-name-hash)) ids))]
    [`(return ,aexp) (return (parse-one aexp fn-name-hash))]
    [`(skip) (skip)]
    ['true #t]
    ['false #f]
    [(? symbol? id) id] ;; (string->symbol (string-append "_" (symbol->string id)))
    [`(,(? symbol? nm) ,args ...) (error "undefined")]
    [(? list? x) (error "incorrect")]
    [x x]))

(define (parse-body code fn-name-hash)
  (match code
  [`(vars [(,ids ,nums) ...] ,stmts ...)
   (define vars (make-hash))
   (for ([id ids] [num nums])
     (hash-set! vars id num))
   (cond
     [(not (= (length ids) (hash-count vars))) (error "duplicate")]
     [else 
      (define result (parse-res vars (map (λ (s) (parse-one s fn-name-hash)) stmts)))
      (if (and (not (empty? (parse-res-ins-lst result))) (return? (last (parse-res-ins-lst result))))
          result
          (error "return"))])]
  [_ (error "bad body shape")]))

(define (parse code)
  (define fn-name-hash
  (for/hash ([x code])
    (match x
      [`(fun (,nm ,ids ...) ,bdy)
       (values nm (length ids))]
      [_ (error "bad function shape")])))
  (cond
    [(not (= (hash-count fn-name-hash) (length code))) (error "duplicate")]
    [else 
     (values
      fn-name-hash
      (map (λ (x)
             (match x
               [`(fun (,nm ,ids ...) ,bdy)
                (fn nm ids (parse-body bdy fn-name-hash))]
               [_ (error "bad function shape")]))
           code))]))

(define (compile-one stmt nparams env fn-name-hash)
  (match stmt
    [(print-a aexp) (append (compile-one aexp nparams env fn-name-hash)
                            (list `(print-val (-1 sp)))
                            (list `(sub sp sp 1)))]
    [(print-s str) (list `(print-string ,str))]
    [(set id aexp) (append (compile-one aexp nparams env fn-name-hash)
                           (list `(move (,(hash-ref env id (λ () (error "undefined variable ~a" id))) fp) (-1 sp))
                                 `(sub sp sp 1)))]
    [(seq stmts) (append-map (λ (s) (compile-one s nparams env fn-name-hash)) stmts)]
    [(iif bexp stmt1 stmt2) (define lab1 (string->symbol (format "LABEL~a" labcount)))
                            (define lab2 (string->symbol (format "LABEL~a" (+ 1 labcount))))
                            (define lab3 (string->symbol (format "LABEL~a" (+ 2 labcount))))
                            (set! labcount (+ labcount 3))
                            (define temp (append (compile-one bexp nparams env fn-name-hash)
                                                 (list `(branch (-1 sp) ,lab1)
                                                       `(jump ,lab2)
                                                       `(label ,lab1))
                                                 (compile-one stmt1 nparams env fn-name-hash)
                                                 (list `(jump ,lab3)
                                                       `(label ,lab2))
                                                 (compile-one stmt2 nparams env fn-name-hash)
                                                 (list `(label ,lab3)
                                                       `(sub sp sp 1))))
                            temp]
    [(skip) empty]
    [(while bexp stmts) (define lab1 (string->symbol (format "LABEL~a" labcount)))
                        (define lab2 (string->symbol (format "LABEL~a" (+ 1 labcount))))
                        (define lab3 (string->symbol (format "LABEL~a" (+ 2 labcount))))
                        (set! labcount (+ labcount 3))
                        (define temp (append (list `(label ,lab1))
                                             (compile-one bexp nparams env fn-name-hash)
                                             (list `(branch (-1 sp) ,lab2)
                                                   `(jump ,lab3)
                                                   `(label ,lab2))
                                             (append-map (λ (s) (compile-one s nparams env fn-name-hash)) stmts)
                                             (list `(sub sp sp 1))
                                             (list `(jump ,lab1)
                                                   `(label ,lab3)
                                                   `(sub sp sp 1))))
                        temp]
    [(bin/op op aexp1 aexp2) (append (compile-one aexp1 nparams env fn-name-hash)
                                     (compile-one aexp2 nparams env fn-name-hash)
                                     (list `(,op (-2 sp) (-2 sp) (-1 sp))
                                           `(sub sp sp 1)))]
    [(fn-call nm args)
     (if (= (length args) (hash-ref fn-name-hash nm))
         (let ([nargs (length args)])
           (append
            (append-map (λ (s) (compile-one s nparams env fn-name-hash)) args)
            (for/list ([i (in-range (sub1 nargs) -1 -1)])
              `(move (,(+ (- nargs) i 3) sp)
                     (,(+ (- nargs) i) sp)))
            (list `(move (,(- nargs) sp) fp)
                  `(jsr (,(+ 1 (- nargs)) sp)
                        ,(string->symbol (string-append "FN_" (symbol->string nm))))
                  `(move (0 sp) (2 sp))
                  `(add sp sp 1))))
         (error "arguments"))]
    [(snot bexp) (append (compile-one bexp nparams env fn-name-hash)
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
                                                (append (compile-one x nparams env fn-name-hash)
                                                        (list `(lnot (0 sp) (-1 sp))
                                                              `(add sp sp 1)
                                                              `(branch (-1 sp) ,lab-short)
                                                              `(sub sp sp 2))))
                                              init-bexps)
                                  (compile-one last-bexp nparams env fn-name-hash)
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
                                                            (append (compile-one x nparams env fn-name-hash)
                                                                    (list `(branch (-1 sp) ,lab1)
                                                                          `(sub sp sp 1))))
                                                          init-bexps)
                                              (compile-one last-bexp nparams env fn-name-hash)
                                              (list `(label ,lab1))))
                         temp])]
    [(return aexp) (append (compile-one aexp nparams env fn-name-hash)
                           (list `(move (2 fp) (-1 sp))
                                 `(move sp fp)
                                 `(move fp (0 fp))
                                 `(jump (1 sp))))]
    [(? (λ (s) (and (symbol? s) (not (boolean? s)))) x) (list `(move (0 sp) (,(hash-ref env x (λ () (error "undefined variable ~a" x))) fp))
                                                              `(add sp sp 1))]
    [x (list `(move (0 sp) ,x)
             `(add sp sp 1))]))
  
(define (compile-body parsed-bdy nparams env fn-name-hash)
  (define stmts (parse-res-ins-lst parsed-bdy))
  (append-map (λ (s) (compile-one s nparams env fn-name-hash)) stmts))
  
(define (compile-fn f fn-name-hash)
  (match f
    [(fn nm ids bdy)
     (define start-lab `(label ,(string->symbol (string-append "FN_" (symbol->string nm)))))
     (define nparams (length ids))
     (define locals (parse-res-var-hash bdy))

     (define param-env
       (for/hash ([id ids] [i (in-naturals 3)])
         (values id i)))

     (define local-env
       (for/hash ([k (in-list (sort (hash-keys locals) symbol<?))]
                  [i (in-naturals (+ nparams 3))])
         (values k i)))

     (define env param-env)
     (for ([(k v) (in-hash local-env)])
       (set! env (hash-set env k v)))
  
     (cond
       [(not (= (hash-count env) (+ (hash-count local-env) nparams))) (error "duplicate")]
       [else 
        (define comp-bdy (compile-body bdy nparams env fn-name-hash))
        (define local-def
          (for/list ([k (in-list (sort (hash-keys locals) symbol<?))])
            `(move (,(hash-ref env k) fp) ,(hash-ref locals k))))
        (define prologue
          (list `(sub fp sp ,nparams)
                `(add sp sp ,(+ 3 (hash-count locals)))))
        (append (list start-lab)
                prologue
                local-def
                comp-bdy)])]
    [_ (error "bad parsed function")]))

(define (compile-simpl code)
  (set! labcount 0)
  (define-values (fn-name-hash parsed) (parse code))
  (define compiled (append-map (λ (f) (compile-fn f fn-name-hash)) parsed))
  (cond
    [(not (hash-has-key? fn-name-hash 'main)) (append (list `(const stadrr stack)
                                                            `(move sp stadrr)
                                                            `(move (0 sp) 0)
                                                            `(halt))
                                                      compiled
                                                      (list `(data stack (10000 0))
                                                            `(data sp 0)
                                                            `(data fp 0)))]
    [(not (zero? (hash-ref fn-name-hash 'main))) (error "arguments")]
    [else (append (list `(const stadrr stack)
                        `(move sp stadrr)
                        `(move (0 sp) 0)
                        `(jsr (1 sp) FN_main)
                        `(halt))
                  compiled
                  (list `(data stack (9000 0))
                        `(data sp 0)
                        `(data fp 0)))]))
