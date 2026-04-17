#lang racket

(provide primplify)

(define memo-table (make-hash))
(define (resolve-sym h e vis)
  (cond
    [(hash-has-key? memo-table e) (hash-ref memo-table e)]
    [(not (hash-has-key? h e)) (error "Error: undefined psymbol" e)]
    [(hash-has-key? vis e) (error "Error: circular psymbol" e)]
    [else
     (define res (hash-ref h e))
     (define val
       (cond
         [(or (number? (cadr res)) (boolean? (cadr res))) (cadr res)]
         [else (resolve-sym h (cadr res) (hash-set vis e true))]))
     (hash-set! memo-table e val)
     val]))

(define (resolve-datalists h e)
  (define res (hash-ref h e))
  (cond
    [(equal? 'data-s (car res)) (cond
                                  [(or (number? (cadddr res)) (boolean? (cadddr res))) (cadddr res)]
                                  [(hash-has-key? memo-table (cadddr res)) (hash-ref memo-table (cadddr res))]
                                  [else (error "Error: undefined psymbol" (cadddr res))])]
    [(equal? 'data (car res)) (map (λ (x) (cond
                                            [(or (boolean? x) (number? x)) x]
                                            [(hash-has-key? memo-table x) (hash-ref memo-table x)]
                                            [else (error "Error: undefined psymbol" x)]))
                                   (caddr res))]
    [else (error "how did we get here?")]))

(define (resolve-imm imm)
  (cond
    [(or (number? imm) (boolean? imm)) imm]
    [else (hash-ref memo-table imm (λ () (error "Error: undefined psymbol" imm)))]))
(define (resolve-ind ind)
  (cond
    [(natural? ind) ind] 
    [else (hash-ref memo-table ind (λ () (error "Error: undefined psymbol" ind)))]))

(define (valid-tri? nm)
  (or (equal? nm 'add)
      (equal? nm 'sub)
      (equal? nm 'mul)
      (equal? nm 'div)
      (equal? nm 'mod)
      (equal? nm 'gt)
      (equal? nm 'ge)
      (equal? nm 'lt)
      (equal? nm 'le)
      (equal? nm 'equal)
      (equal? nm 'not-equal)
      (equal? nm 'land)
      (equal? nm 'lor)))

(define (primplify ins-lst)
  ;; pass 1: collect parts of the program which require 2-pass parsing (a-primpl \ {halt})
  (set! memo-table (make-hash))
  (define addr 0)
  (define hash-lst (make-hash))
  (for ([x ins-lst])
    (match x
      [`(label ,ps) (if (hash-has-key? hash-lst ps)
                        (error "Error: duplicate of psymbol (label)" ps)
                        (hash-set! hash-lst ps (list 'label addr)))]
      [`(const ,ps ,thing) (if (hash-has-key? hash-lst ps)
                               (error "Error: duplicate of psymbol (const)" ps)
                               (hash-set! hash-lst ps (list 'const thing)))]
      [`(data ,ps1 (,n ,ps2)) (if (hash-has-key? hash-lst ps1)
                                  (error "Error: duplicate of psymbol (datalist)" ps1)
                                  (begin
                                    (hash-set! hash-lst ps1 (list 'data-s addr n ps2))
                                    (set! addr (+ addr n))))]
      [`(data ,ps ,pses ...) (if (hash-has-key? hash-lst ps)
                                 (error "Error: duplicate of psymbol (datalist)" ps)
                                 (begin
                                   (hash-set! hash-lst ps (list 'data addr pses))
                                   (set! addr (+ addr (length pses)))))]
      [x (set! addr (add1 addr))]))

  ;; resolve symbols (graph theory :))
  (define hash-lst2 (make-hash))
  (for ([k (in-hash-keys hash-lst)])
    (define temp (hash-ref hash-lst k))
    (hash-set! hash-lst2 k (cons (car temp) (cons (resolve-sym hash-lst k (hash)) (cddr temp)))))
  (for ([k (filter (λ (x)
                     (define lst (hash-ref hash-lst2 x))
                     (or (equal? 'data (car lst)) (equal? 'data-s (car lst))))
                   (hash-keys hash-lst2))])
    (define temp2 (hash-ref hash-lst2 k))
    (if (equal? 'data (car temp2))
        (hash-set! hash-lst2 k (list (car temp2) (cadr temp2) (resolve-datalists hash-lst2 k)))
        (hash-set! hash-lst2 k (list (car temp2) (cadr temp2) (caddr temp2) (resolve-datalists hash-lst2 k)))))

  #|
  (cond
              [(symbol? op) (define check (hash-ref hash-lst2 op (λ () (error "Error: undefined psymbol" op))))
                            (error "Error: incorrect use of psymbol" op)]
              [else (list op)])
  |#

  ;; (error "Error: incorrect use of psymbol ~a" (cadddr res))
  ;; pass 2: build new list of instructions
  (define (resolve-ind-opd opd)
  (match opd
    [`(,op) (list op)]
    [(? symbol? s)
     (define check (hash-ref hash-lst2 s (λ () (error "Error: undefined psymbol" s))))
     (cond
       [(or (equal? 'data (car check)) (equal? 'data-s (car check))) (list (cadr check))]
       [else (error "Error: incorrect use of psymbol" s)])]
    [op op]))
  (define (resolve-idx-imm op)
  (cond
    [(symbol? op)
     (define info (hash-ref hash-lst2 op (λ () (error "Error: undefined psymbol" op))))
     (if (equal? 'label (car info))
         (error "Error: incorrect use of psymbol" op)
         (hash-ref memo-table op))]
    [else op]))
  (define (resolve-jump-opd opd)
    (match opd
      [`(,op) (list op)]
      [`(,op1 ,op2) (list (resolve-idx-imm op1) (resolve-ind-opd op2))]
      [op (cond
            [(symbol? op)
             (define check (hash-ref hash-lst2 op (λ () (error "Error: undefined psymbol" op))))
             (cond
               [(equal? 'label (car check)) (resolve-imm op)]
               [(or (equal? 'data (car check)) (equal? 'data-s (car check))) (list (resolve-ind op))]
               [(equal? 'const (car check)) (list (resolve-imm op))]
               [else (error "Error: incorrect use of psymbol" op)])]
            [else op])]))
  (define (resolve-opd opd)
    (match opd
      [`(,op) (list op)]
      [`(,op1 ,op2) (list (resolve-idx-imm op1) (resolve-ind-opd op2))]
      [op (cond
            [(or (number? op) (boolean? op)) op]
            [(symbol? op)
             (define check (hash-ref hash-lst2 op (λ () (error "Error: undefined psymbol" op))))
             (cond
               [(or (equal? 'data (car check)) (equal? 'data-s (car check))) (list (resolve-ind op))]
               [(equal? 'const (car check)) (resolve-imm op)]
               [else (error "Error: incorrect use of psymbol" op)])]
            [else op])]))
  (define (resolve-dest dest)
    (match dest
      [`(,op) (list op)]
      [`(,op1 ,op2) (list (resolve-idx-imm op1) (resolve-ind-opd op2))]
      [op (cond
            [(symbol? op)
             (define check (hash-ref hash-lst2 op (λ () (error "Error: undefined psymbol" op))))
             (if (or (equal? 'const (car check)) (equal? 'label (car check)))
                 (error "Error: incorrect use of psymbol" op)
                 (list (cadr check)))]
            [else op])]))
  
  (define (match-one ins)
    (match ins
      [`(jump ,opd) (list (list 'jump (resolve-jump-opd opd)))]
      [`(branch ,op1 ,op2) (list (list 'branch (resolve-opd op1) (resolve-jump-opd op2)))]
      [`(move ,dest ,opd) (list (list 'move (resolve-dest dest) (resolve-opd opd)))]
      [`(print-val ,opd) (list (list 'print-val (resolve-opd opd)))]
      [`(print-string ,string) (list (list 'print-string string))]
      [`(lnot ,dest ,opd) (list (list 'lnot (resolve-dest dest) (resolve-opd opd)))]
      [`(,(and op (? valid-tri?)) ,dest ,opd1 ,opd2) (list (list op (resolve-dest dest) (resolve-opd opd1) (resolve-opd opd2)))]
      [`(const ,ps ,psv) empty]
      [`(data ,ps (,n ,sm)) (make-list n (cadddr (hash-ref hash-lst2 ps)))]
      [`(data ,ps ,pses ...) (caddr (hash-ref hash-lst2 ps))]
      [`(label ,ps) empty]
      ['(halt) (list 0)]
      [(? symbol? s) (list (resolve-imm s))]
      [x (list x)]))
  
  (append-map match-one ins-lst))
    
      