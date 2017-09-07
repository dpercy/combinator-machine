#lang racket

(require (prefix-in racket: racket))
(module+ test (require rackunit))


(define prim? (or/c 'S 'K 'I 'B 'C 'P 'U '+))
(define keyword? (or/c 'fn))
(define var? (and/c symbol? (not/c prim?) (not/c keyword?)))

(define pattern?
  (flat-rec-contract pattern?
                     (or/c var?
                           (list/c (list/c 'P pattern?) pattern?))))
(define expr? ; open terms + lambda
  (flat-rec-contract expr?
                     (or/c prim?
                           number?
                           (list/c expr? expr?)
                           var?
                           (list/c 'fn pattern? expr?))))
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
  (check-pred expr-only? '(fn x x))
  (check-pred expr-only? '(fn ((P x) y) x))
  (check-pred bad? '(fn (P x) x)) ; P pattern missing an arg
  (check-pred bad? '(fn (x y) 42)) ; not fully curried

  )


(define/contract (free-vars term) (-> expr? (set/c var?))
  (match term
    [(? prim?) (set)]
    [(? number?) (set)]
    [(list f a) (set-union (free-vars f) (free-vars a))]
    [(? var? x) (set x)]
    [`(fn ,x ,e) (set-subtract (free-vars e) (free-vars x))]))
(define closed?
  (let ([closed? (lambda (e) (set-empty? (free-vars e)))])
    (and/c expr? closed?)))
(module+ test
  (check-equal? (free-vars '(fn x ((K x) y)))
                (set 'y))
  (check-pred closed?  '(fn x (((K x) +) 4))))

; give each term a meaning in Racket (strict semantics)
(define/contract (eval term) (-> term? any/c)
  (match term
    ['S (lambda (x) (lambda (y) (lambda (z) ((x z) (y z)))))]
    ['K (lambda (x) (lambda (y) x))]
    ['I (lambda (x) x)]
    ['B (lambda (f) (lambda (g) (lambda (x) (f (g x)))))]
    ['C (lambda (f) (lambda (g) (lambda (x) ((f x) g))))]
    ['P (lambda (hd) (lambda (tl) (cons hd tl)))]
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
    [`(fn ,x ,e) (abs x (compile-expr e))]))
(define/contract compile (-> closed? term?) compile-expr)
(define/contract (abs binder expr) (-> pattern? combination? combination?)
  ; TODO support patterns
  ; TODO tighten the contract? binder not free in output.
  (match* {binder expr}
    [{x (list e1 e2)} (S (abs x e1) (abs x e2))]
    [{`((P ,p1) ,p2) e} `(U ,(abs p1 (abs p2 e)))]
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
  (check-equal? ((eval (compile '(fn n ((+ n) n)))) 4) 8)
  (check-equal? ((eval (compile '(U +))) (cons 100 10)) 110)

  (check-equal? (compile '(fn x ((+ 40) x))) '(+ 40))


  ; S threads a free variable through a function application
  (check-equal? (compile '(fn x ((P x) (+ x))))
                '((S P) +))
  (check-match ((eval '((S P) +)) 100)
               (cons 100 (? procedure? f))
               (equal? (f 3) 103))

  ; K is the constant operator
  (check-equal? (compile '(fn x 42)) '(K 42))
  (check-equal? ((eval '(K 42)) 1337) 42)

  ; C is like a right operator section: (C + 40) == (_ + 40)
  (check-equal? (compile '(fn x ((+ x) 40))) '((C +) 40))
  (check-equal? ((eval '((C +) 40)) 2) 42)
  (check-equal? ((eval '((C P) 40)) 2) (cons 2 40))

  ; B is the compose operator: B f g x == f (g x)
  (check-equal? (compile '(fn x ((+ 2) ((+ 10) x))))
                '((B (+ 2)) (+ 10)))
  (check-equal? ((eval '((B (+ 2)) (+ 10))) 3) 15)
  (check-equal? ((eval '((B (P 2)) (P 10))) 3) (list* 2 10 3))

  ; U is "uncurry" for destructuring pairs
  (check-equal? (compile '(fn ((P x) y) x)) '(U K))
  (check-equal? (compile '(fn ((P x) y) y)) '(U (K I)))


  ; Can I repro the "self optimization" Turner mentioned?




  ;;
  )
