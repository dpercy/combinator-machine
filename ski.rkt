#lang racket

(require (prefix-in racket: racket))
(module+ test (require rackunit))

#|

S f g x = f x (g x)
K x y   = x
I x     = x
B f g x = f (g x)
C f x y = f y x

U f p   = (f (exl p)) (exr p)


what if we add a combinator "seq"?
seq x f = f x,
but (seq x) is only a value if x is a value.
so then ((+ x) y) becomes
seq x ((C +) y)

this is like case.
case x { handlers ... }

maybe the args stack can contain case handlers.

maybe there's just a type for "strict lambda"



|#

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
    ['S (lambda (f) (lambda (g) (lambda (x) ((f x) (g x)))))]
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
  ; TODO more optimizations: http://haskell.cs.yale.edu/wp-content/uploads/2011/03/CombComp-POPL84.pdf
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
  ; or C is like "flip"
  (check-equal? (eval '(((C P) 1) 2)) (cons 2 1))

  ; B is the compose operator: B f g x == f (g x)
  (check-equal? (compile '(fn x ((+ 2) ((+ 10) x))))
                '((B (+ 2)) (+ 10)))
  (check-equal? ((eval '((B (+ 2)) (+ 10))) 3) 15)
  (check-equal? ((eval '((B (P 2)) (P 10))) 3) (list* 2 10 3))

  ; U is "uncurry" for destructuring pairs
  (check-equal? (compile '(fn ((P x) y) x)) '(U K))
  (check-equal? (compile '(fn ((P x) y) y)) '(U (K I)))



  ; Let's look at nontermination
  (define omega (compile '((fn x (x x)) (fn x (x x)))))
  (check-equal? omega '(((S I) I) ((S I) I)))
  (define delay-omega (compile `(fn x ,omega)))
  (check-equal? delay-omega `(K ,omega))
  ; Even though delay-omega is a lambda form, this eval will diverge.
  ; The problem is our compilation rules assume eta-reduction is legal,
  ; and this throws away the (fn x _) wrapper that was intended to
  ; control side effects.
  ;;;(check-pred procedure? (eval delay-omega))
  ; Maybe the best thing is to use a lazy semantics.

  (define Y (compile '(fn f ((fn x ((f x) x)) (fn x ((f x) x))))))


  ; TODO implement a lazy interpreter (big step to Racket? big step rewriter? small step rewriter?)

  ; TODO repro the "self optimizing" thing
  ;  - requires a mutable term graph?

  ; TODO extend pattern matching to work with other constructors
  ;  - maybe generalize U to have a fallback case
  ;  - also wait: what does (P x) or (S f) mean?
  ;    - normally a curried constructor can't be taken apart
  ;    - but now the goal is to inspect any partially applied function

  ; TODO try symbolic differentiation on SKI



  ;;
  )



(struct App (f a) #:transparent #:mutable)

(define/contract (term->graph term) (-> term? any/c)
  ; TODO memoize for some free sharing
  (match term
    [(? prim? p) p]
    [(? number? n) n]
    [(list f a) (App (term->graph f) (term->graph a))]))

(define (update! dst f a)
  (set-App-f! dst f)
  (set-App-a! dst a)
  (void))

; takes a graph as input.
; reduces it in place to a value (or (App 'I value)).
; also returns the value (without the I wrapper).
(define (run! graph)
  (r! (list graph)))
(define (r! stack)
  (define (ret) (foldl (lambda (a f) (App f a)) (first stack) (rest stack)))
  (match stack
    [(list* 'S f g x stack) (r! (list* f x (App g x) stack))]
    [(list* 'K x y stack) (r! (list* x stack))]
    [(list* 'I x stack) (r! (list* x stack))]
    [(list* 'B f g x stack) (r! (list* f (App g x) stack))]
    [(list* 'C f x y stack) (r! (list* f y x stack))]
    [(list* '+ x y stack) (match* {(run! x) (run! y)}
                            [{(? number? x) (? number? y)} (r! (list* (+ x y) stack))]
                            [{x y} (error '+ "non-number: ~v ~v" x y)])]
    [(list* 'inc stack) (r! (list* '+ 1 stack))]
    [(list* (App f a) stack) (r! (list* f a stack))]
    ; finally, if no rewrite rule applies,
    ; the top of the stack must be either:
    ; - a value
    ; - a constructor
    ; - something you're not allowed to apply, being applied
    [(list (? number? n)) n]
    [(list 'P x y) (ret)]
    [(list* (and f (or 'S 'K 'I 'B 'C '+)) args) (ret)]
    [_ (error 'r! "no rule for stack: ~v" stack)]))
(module+ test


  (check-equal? (run! (App 'inc 0))
                1)

  (check-equal? (run! (App 'inc (App 'inc 0)))
                2)

  (check-equal? (run! (App 'inc (App 'inc (App 'inc (App 'inc (App 'inc (App 'inc 0)))))))
                6)


  (check-equal? (run! (App (App '+ 1) 2))
                3)

  (check-exn exn:fail?
             (lambda () (run! (App 1 2))))

  (check-equal? (run! (App (App '+ (App (App '+ 1) 2)) 3))
                6)

  (check-equal? (run! (App (App '+ 1) (App (App '+ 2) 3)))
                6)

  ; computed functions:
  ; - I rule
  (check-equal? (run! (App (App (App 'I '+) 1) 2))
                3)
  ; - K rule
  (check-equal? (run! (App (App (App (App 'K '+) 7) 1) 2))
                3)
  ; - S rule: S + inc 3 => + 3 (inc 3) => + 3 4 => 7
  (check-equal? (run! (App (App (App 'S '+) 'inc) 3))
                7)


  (check-equal? (run! (App (App (App 'C 'P) 1) 2))
                (App (App 'P 2) 1))
  (check-exn exn:fail?
             (lambda () (run! (App (App (App (App 'C 'P) 1) 2) 3))))

  ; partially applied combinator is a value
  (check-equal? (run! (App (App 'S 1) 2))
                (App (App 'S 1) 2))

  ; constructors are lazy
  (check-equal? (run! (App (App (App 'C 'P) (App 'I 'K)) (App 'I (App 'I (App 'I 'K)))))
                (App (App 'P (App 'I (App 'I (App 'I 'K))))
                     (App 'I 'K)))

  ;;
  )
