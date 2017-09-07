#lang racket

(require (prefix-in racket: racket))
(module+ test (require rackunit))


(define prim? (or/c 'S 'K 'I 'B 'C 'cons 'U '+))
(define keyword? (or/c 'lambda))
(define var? (and/c symbol? (not/c prim?) (not/c keyword?)))

(define expr? ; open terms + lambda
  (flat-rec-contract expr?
                     (or/c prim?
                           number?
                           (list/c expr? expr?)
                           var?
                           (list/c 'lambda (list/c var?) expr?))))
(define combination? ; open terms
  (flat-rec-contract term?
                     (or/c prim?
                           number?
                           (list/c term? term?)
                           var?)))
(define term?
  (flat-rec-contract term?
                     (or/c prim?
                           number?
                           (list/c term? term?))))
(module+ test

  (define expr-only? (and/c expr? (not/c term?)))
  (define bad? (not/c expr?))

  (check-pred term? 5)
  (check-pred term? '(I 5))
  (check-pred term? '(+ 2)) ; evaluates to (lambda (x) (+ 2 x))
  (check-pred term? '((+ 2) 4))
  (check-pred bad? '(+ 2 3)) ; not fully curried
  (check-pred expr-only? '(lambda (x) x))
  (check-pred bad? '(lambda (x y) 42)) ; not fully curried

  )


(define/contract (free-vars term) (-> expr? (set/c var?))
  (match term
    [(? prim?) (set)]
    [(? number?) (set)]
    [(list f a) (set-union (free-vars f) (free-vars a))]
    [(? var? x) (set x)]
    [`(lambda (,x) ,e) (set-remove (free-vars e) x)]))
(define closed? (and/c expr? (compose set-empty? free-vars)))
(module+ test
  (check-equal? (free-vars '(lambda (x) ((K x) y)))
                (set 'y))
  (check-pred closed?  '(lambda (x) (((K x) +) 4))))

; give each term a meaning in Racket (strict semantics)
(define/contract (eval term) (-> term? any/c)
  (match term
    ['S (lambda (x) (lambda (y) (lambda (z) ((x z) (y z)))))]
    ['K (lambda (x) (lambda (y) x))]
    ['I (lambda (x) x)]
    ['B (lambda (f) (lambda (g) (lambda (x) (f (g x)))))]
    ['C (lambda (f) (lambda (g) (lambda (x) ((f x) g))))]
    ['cons (lambda (hd) (lambda (tl) (cons hd tl)))]
    ['U (lambda (f) (lambda (pair) ((f (car pair)) (cdr pair))))]
    ['+ (lambda (x) (lambda (y) (+ x y)))]
    [(? number? n) n]
    [(list f a) ((eval f) (eval a))]))

; translate lambda expressions into core terms
(define/contract (compile-expr expr) (-> expr? combination?)
  (match expr
    [(? prim? p) p]
    [(? number? n) n]
    [(list f a) (list (compile-expr f) (compile-expr a))]
    [(? var? x) x]
    [`(lambda (,x) ,e) (abs x (compile-expr e))]))
(define/contract compile (-> closed? term?) compile-expr)
(define/contract (abs binder expr) (-> var? combination? combination?)
  ; TODO support patterns
  ; TODO tighten the contract? binder not free in output.
  (match* {binder expr}
    [{x (list e1 e2)} (S (abs x e1) (abs x e2))]
    [{x x} 'I]
    [{x y} `(K ,y)]))
; smart constructor for S:
; if one or both arguments are constant, we can avoid plumbing an ignored
; value everywhere.
(define/contract (S e1 e2) (-> combination? combination? combination?)
  (match* {e1 e2}
    [{`(K ,e1) `(K ,e2)} `(K (,e1 ,e2))]
    [{`(K ,e1) 'I} e1]
    [{`(K ,e1) e2} `((B ,e1) ,e2)]
    [{e1 `(K ,e2)} `((C ,e1) ,e2)]
    [{e1 e2} `((S ,e1) ,e2)]))
(module+ test

  (check-equal? (eval (compile '((+ 2) 3))) 5)
  (check-equal? ((eval (compile '(+ 40))) 2) 42)
  (check-equal? ((eval (compile '(lambda (n) ((+ n) n)))) 4) 8)
  (check-equal? ((eval (compile '(U +))) (cons 100 10)) 110)

  (check-equal? (compile '(lambda (x) ((+ 40) x))) '(+ 40))


  ; S threads a free variable through a function application
  (check-equal? (compile '(lambda (x) ((cons x) (+ x))))
                '((S cons) +))
  (check-match ((eval '((S cons) +)) 100)
               (cons 100 (? procedure? f))
               (equal? (f 3) 103))

  ; K is the constant operator
  (check-equal? (compile '(lambda (x) 42)) '(K 42))
  (check-equal? ((eval '(K 42)) 1337) 42)

  ; C is like a right operator section: (C + 40) == (_ + 40)
  (check-equal? (compile '(lambda (x) ((+ x) 40))) '((C +) 40))
  (check-equal? ((eval '((C +) 40)) 2) 42)
  (check-equal? ((eval '((C cons) 40)) 2) (cons 2 40))

  ; B is the compose operator: B f g x == f (g x)
  (check-equal? (compile '(lambda (x) ((+ 2) ((+ 10) x))))
                '((B (+ 2)) (+ 10)))
  (check-equal? ((eval '((B (+ 2)) (+ 10))) 3) 15)
  (check-equal? ((eval '((B (cons 2)) (cons 10))) 3) (list* 2 10 3))


  ; Can I repro the "self optimization" Turner mentioned?




  ;;
  )
