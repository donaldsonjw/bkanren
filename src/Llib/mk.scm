(module bkanren
   (include "mk.sch")
   (export mk-take
	   bind
	   ==
	   choice
	   empty-f
	   reify walk*
	   var var? eigen-var eigen-absento
	   empty-c
	   (inline make-c b e s d y n g t)
	   ;(syntax make-c)
	   ground?
	   mplus mzero
	   succeed fail unit
	   absento symbolo numbero booleano stringo
	   onceo
	   =/=
	   c->B c->E c->S c->D c->Y c->N c->G c->T
	   else
	   )

   (export
      (final-class %var
	 sym)
      (final-class %package
	 (B (default '()))
	 (E (default '()))
	 (S (default '()))
	 (D (default '()))
	 (Y (default '()))
	 (N (default '()))
	 (G (default '()))
	 (T (default '()))
	 ))
   )
;;; newer version: Sept. 18 2013 (with eigens)
;;; Jason Hemann, Will Byrd, and Dan Friedman
;;; E = (e* . x*)*, where e* is a list of eigens and x* is a list of variables.
;;; Each e in e* is checked for any of its eigens be in any of its x*.  Then it fails.
;;; Since eigen-occurs-check is chasing variables, we might as will do a memq instead
;;; of an eq? when an eigen is found through a chain of walks.  See eigen-occurs-check.
;;; All the e* must be the eigens created as part of a single eigen.  The reifier just
;;; abandons E, if it succeeds.  If there is no failure by then, there were no eigen
;;; violations.


;; add missing r6rs remp function
(define (remp proc list)
   (filter (lambda (x) (not (proc x))) list))


;; add missing exists function
;; simplified version of r6rs function
;; only accepts a single list
(define (exists proc lst)
   (let loop ((l lst))
      (if (pair? l)
	  (let ((curr (car l)))
	     (if (proc curr)
		 curr
		 (loop (cdr l))))
	  #f)))

;; original minikanren file
(define c->B (lambda (c::%package) (-> c B)))
(define c->E (lambda (c::%package) (-> c E)))
(define c->S (lambda (c::%package) (-> c S)))
(define c->D (lambda (c::%package) (-> c D)))
(define c->Y (lambda (c::%package) (-> c Y)))
(define c->N (lambda (c::%package) (-> c N)))
(define c->G (lambda (c::%package) (-> c G)))
(define c->T (lambda (c::%package) (-> c T)))

(define empty-c (instantiate::%package))

(define-inline (make-c b e s d y n g t)
   (instantiate::%package (B b) (E e) (S s) (D d) (Y y) (N n) (G g) (T t))
   )
; (define-syntax make-c (syntax-rules ()
;  ([_ b e s d y n g t]
;    (instantiate::%package (B b) (E e) (S s) (D d) (Y y) (N n) (G g) (T t))
;    )))

(define eigen-tag (vector 'eigen-tag))

(define rhs
  (lambda (pr)
    (cdr pr)))
 
(define lhs
  (lambda (pr)
    (car pr)))

(define eigen-var
  (lambda ()
    (vector eigen-tag)))

(define eigen?
  (lambda (x)
    (and (vector? x) (eq? (vector-ref x 0) eigen-tag))))

(define var (lambda (dummy)::symbol (instantiate::%var (sym dummy))))

(define var? (lambda (x) (isa? x %var)))

; (define var
;   (lambda (dummy)
;     (vector dummy)))

; (define var?
;   (lambda (x)
;     (and (vector? x) (not (eq? (vector-ref x 0) eigen-tag)))))

(define walk
  (lambda (u S)
    (cond
      ((and (var? u) (assq u S)) =>
       (lambda (pr) (walk (rhs pr) S)))
      (else u))))

(define prefix-S
  (lambda (S+ S)
    (cond
      ((eq? S+ S) '())
      (else (cons (car S+)
              (prefix-S (cdr S+) S))))))

(define unify
  (lambda (u v s)
    (let ((u (walk u s))
          (v (walk v s)))
      (cond
        ((eq? u v) s)
        ((var? u) (ext-s-check u v s))
        ((var? v) (ext-s-check v u s))
        ((and (pair? u) (pair? v))
         (let ((s (unify (car u) (car v) s)))
           (and s (unify (cdr u) (cdr v) s))))
        ((or (eigen? u) (eigen? v)) #f)
        ((equal? u v) s)
        (else #f)))))

(define occurs-check
  (lambda (x v s)
    (let ((v (walk v s)))
      (cond
        ((var? v) (eq? v x))
        ((pair? v) 
         (or 
           (occurs-check x (car v) s)
           (occurs-check x (cdr v) s)))
        (else #f)))))

(define eigen-occurs-check
  (lambda (e* x s)
    (let ((x (walk x s)))
      (cond
        ((var? x) #f)
        ((eigen? x) (memq x e*))
        ((pair? x) 
         (or 
           (eigen-occurs-check e* (car x) s)
           (eigen-occurs-check e* (cdr x) s)))
        (else #f)))))

(define empty-f (lambdaf@ () (mzero)))

(define ext-s-check
  (lambda (x v s)
    (cond
      ((occurs-check x v s) #f)
      (else (cons `(,x . ,v) s)))))

(define unify*  
  (lambda (S+ S)
    (unify (map lhs S+) (map rhs S+) S)))
 


(define bind
  (lambda (c-inf g)
    (case-inf c-inf
      (() (mzero))
      ((f) (inc (bind (f) g)))
      ((c) (g c))
      ((c f) (mplus (g c) (lambdaf@ () (bind (f) g)))))))


 
(define mk-take
  (lambda (n f)
    (cond
      ((and n (zero? n)) '())
      (else
       (case-inf (f) 
         (() '())
         ((f) (mk-take n f))
         ((c) (cons c '()))
         ((c f) (cons c
                  (mk-take (and n (- n 1)) f))))))))


 
(define mplus
  (lambda (c-inf f)
    (case-inf c-inf
      (() (f))
      ((f^) (inc (mplus (f) f^)))
      ((c) (choice c f))
      ((c f^) (choice c (lambdaf@ () (mplus (f) f^)))))))




(define mzero (lambda () #f))

(define unit (lambda (c) c))

(define choice (lambda (c f) (cons c f)))

(define tagged?
  (lambda (S Y y^)
    (exists (lambda (y) (eqv? (walk y S) y^)) Y)))

(define untyped-var?
  (lambda (S Y N t^)
    (let ((in-type? (lambda (y) (eq? (walk y S) t^))))
      (and (var? t^)
           (not (exists in-type? Y))
           (not (exists in-type? N))))))



(define walk*
  (lambda (v S)
    (let ((v (walk v S)))
      (cond
        ((var? v) v)
        ((pair? v)
         (cons (walk* (car v) S) (walk* (cdr v) S)))
        (else v)))))

(define reify-S
  (lambda  (v S)
    (let ((v (walk v S)))
      (cond
        ((var? v)
         (let ((n (length S)))
           (let ((name (reify-name n)))
             (cons `(,v . ,name) S))))
        ((pair? v)
         (let ((S (reify-S (car v) S)))
           (reify-S (cdr v) S)))
        (else S)))))

(define reify-name
  (lambda (n)
    (string->symbol
      (string-append "_" "." (number->string n)))))

(define drop-dot
  (lambda (X)
    (map (lambda (t)
           (let ((a (lhs t))
                 (d (rhs t)))
             `(,a ,d)))
         X)))

(define sorter
  (lambda (ls)
    (sort lex<=? ls)))
                              
(define lex<=?
  (lambda (x y)
    (string<=? (datum->string x) (datum->string y))))
  
(define datum->string
  (lambda (x)
    (call-with-output-string
      (lambda (p) (display x p)))))

(define anyvar? 
  (lambda (u r)
    (cond
      ((pair? u)
       (or (anyvar? (car u) r)
           (anyvar? (cdr u) r)))
      (else (var? (walk u r))))))

(define (ground? u)
  (lambda (S)
    (not (anyvar? u S))))

(define anyeigen? 
  (lambda (u r)
    (cond
      ((pair? u)
       (or (anyeigen? (car u) r)
           (anyeigen? (cdr u) r)))
      (else (eigen? (walk u r))))))

(define member* 
  (lambda (u v)
    (cond
      ((equal? u v) #t)
      ((pair? v)
       (or (member* u (car v)) (member* u (cdr v))))
      (else #f))))

;;;

(define drop-N-b/c-const
  (lambdag@ (c : B E S D Y N G T)
    (let ((const? (lambda (n)
                    (not (var? (walk n S))))))
      (cond
        ((find const? N) =>
         (lambda (n) (make-c B E S D Y (remq1 n N) G T)))
        (else c)))))

(define drop-Y-b/c-const
  (lambdag@ (c : B E S D Y N G T)
    (let ((const? (lambda (y)
                    (not (var? (walk y S))))))
      (cond
	((find const? Y) =>
         (lambda (y) (make-c B E S D (remq1 y Y) N G T)))
        (else c)))))

(define remq1
  (lambda (elem ls)
    (cond
      ((null? ls) '())
      ((eq? (car ls) elem) (cdr ls))
      (else (cons (car ls) (remq1 elem (cdr ls)))))))

(define same-var?
  (lambda (v)
    (lambda (v^)
      (and (var? v) (var? v^) (eq? v v^)))))

(define find-dup
  (lambda (f S)
    (lambda (set)
      (let loop ((set^ set))
        (cond
          ((null? set^) #f)
          (else
           (let ((elem (car set^)))
             (let ((elem^ (walk elem S)))
               (cond
                 ((find (lambda (elem^^)
                          ((f elem^) (walk elem^^ S)))
                        (cdr set^))
                  elem)
                 (else (loop (cdr set^))))))))))))

(define drop-N-b/c-dup-var
  (lambdag@ (c : B E S D Y N G T)
    (cond
      (((find-dup same-var? S) N) =>
       (lambda (n) (make-c B E S D Y (remq1 n N) G T)))
      (else c))))

(define drop-Y-b/c-dup-var
  (lambdag@ (c : B E S D Y N G T)
    (cond
      (((find-dup same-var? S) Y) =>
       (lambda (y)
         (make-c B E S D (remq1 y Y) N G T)))
      (else c))))

(define var-type-mismatch?
  (lambda (S Y N G t1^ t2^)
    (cond
      ((num? S N t1^) (not (num? S N t2^)))
      ((sym? S Y t1^) (not (sym? S Y t2^)))
      ((str? S G t1^) (not (str? S G t2^)))
      (else #f))))

(define term-ununifiable?
  (lambda (S Y N G t1 t2)
    (let ((t1^ (walk t1 S))
          (t2^ (walk t2 S)))
      (cond
        ((or (untyped-var? S Y N t1^) (untyped-var? S Y N t2^)) #f)
        ((var? t1^) (var-type-mismatch? S Y N G t1^ t2^))
        ((var? t2^) (var-type-mismatch? S Y N G t2^ t1^))
        ((and (pair? t1^) (pair? t2^))
         (or (term-ununifiable? S Y N G (car t1^) (car t2^))
             (term-ununifiable? S Y N G (cdr t1^) (cdr t2^))))
        (else (not (eqv? t1^ t2^)))))))

(define T-term-ununifiable?
  (lambda (S Y N G)
    (lambda (t1)
      (let ((t1^ (walk t1 S)))
        (letrec
            ((t2-check
              (lambda (t2)
                (let ((t2^ (walk t2 S)))
                  (cond
                    ((pair? t2^) (and
                                  (term-ununifiable? S Y N G t1^ t2^)
                                  (t2-check (car t2^))
                                  (t2-check (cdr t2^))))
                    (else (term-ununifiable? S Y N G t1^ t2^)))))))
          t2-check)))))

(define num?
  (lambda (S N n)
    (let ((n (walk n S)))
      (cond
        ((var? n) (tagged? S N n))
        (else (number? n))))))

(define sym?
  (lambda (S Y y)
    (let ((y (walk y S)))          
      (cond
        ((var? y) (tagged? S Y y))
        (else (symbol? y))))))

(define str?
  (lambda (S G y)
    (let ((n (walk y S)))
      (cond
        ((var? y) (tagged? S G y))
        (else (string? y))))))

(define drop-T-b/c-Y-and-N
  (lambdag@ (c : B E S D Y N G T)
    (let ((drop-t? (T-term-ununifiable? S Y N G)))
      (cond
        ((find (lambda (t) ((drop-t? (lhs t)) (rhs t))) T) =>
         (lambda (t) (make-c B E S D Y N G (remq1 t T))))
        (else c)))))

(define move-T-to-D-b/c-t2-atom
  (lambdag@ (c : B E S D Y N G T)
    (cond
      ((exists (lambda (t)
               (let ((t2^ (walk (rhs t) S)))
                 (cond
                   ((and (not (untyped-var? S Y N t2^))
                         (not (pair? t2^)))
                    (let ((T (remq1 t T)))
                      (make-c B E S `((,t) . ,D) Y N G T)))
                   (else #f))))
             T))
      (else c))))

(define terms-pairwise=?
  (lambda (pr-a^ pr-d^ t-a^ t-d^ S)
    (or
     (and (term=? pr-a^ t-a^ S)
          (term=? pr-d^ t-a^ S))
     (and (term=? pr-a^ t-d^ S)
          (term=? pr-d^ t-a^ S)))))

(define for-all
  (lambda (f ls . more)
    (let for-all ([ls ls] [more more] [a #t])
      (if (null? ls)
          a
          (let ([a (apply f (car ls) (map car more))])
            (and a (for-all (cdr ls) (map cdr more) a)))
	  ))
    ))

(define T-superfluous-pr?
  (lambda (S Y N T)
    (lambda (pr)
      (let ((pr-a^ (walk (lhs pr) S))
            (pr-d^ (walk (rhs pr) S)))
        (cond
          ((exists
               (lambda (t)
                 (let ((t-a^ (walk (lhs t) S))
                       (t-d^ (walk (rhs t) S)))
                   (terms-pairwise=? pr-a^ pr-d^ t-a^ t-d^ S)))
             T)
           (for-all
            (lambda (t)
              (let ((t-a^ (walk (lhs t) S))
                    (t-d^ (walk (rhs t) S)))
                (or
                 (not (terms-pairwise=? pr-a^ pr-d^ t-a^ t-d^ S))
                 (untyped-var? S Y N t-d^)
                 (pair? t-d^))))
            T))
          (else #f))))))

(define drop-from-D-b/c-T
  (lambdag@ (c : B E S D Y N G T)
    (cond
      ((find
           (lambda (d)
             (exists
                 (T-superfluous-pr? S Y N T)
               d))
         D) =>
         (lambda (d) (make-c B E S (remq1 d D) Y N G T)))
      (else c))))

(define drop-t-b/c-t2-occurs-t1
  (lambdag@ (c : B E S D Y N G T)
    (cond
      ((find (lambda (t)
               (let ((t-a^ (walk (lhs t) S))
                     (t-d^ (walk (rhs t) S)))
                 (mem-check t-d^ t-a^ S)))
             T) =>
             (lambda (t)
               (make-c B E S D Y N G (remq1 t T))))
      (else c))))

(define split-t-move-to-d-b/c-pair
  (lambdag@ (c : B E S D Y N G T)
    (cond
      ((exists
         (lambda (t)
           (let ((t2^ (walk (rhs t) S)))
             (cond
               ((pair? t2^) (let ((ta `(,(lhs t) . ,(car t2^)))
                                  (td `(,(lhs t) . ,(cdr t2^))))
                              (let ((T `(,ta ,td . ,(remq1 t T))))
                                (make-c B E S `((,t) . ,D) Y N G T))))
               (else #f))))
         T))
      (else c))))

(define find-d-conflict
  (lambda (S Y N G)
    (lambda (D)
      (find
       (lambda (d)
	 (exists (lambda (pr)
		   (term-ununifiable? S Y N G (lhs pr) (rhs pr)))
		 d))
       D))))

(define drop-D-b/c-Y-or-N
  (lambdag@ (c : B E S D Y N G T)
    (cond
      (((find-d-conflict S Y N G) D) =>
       (lambda (d) (make-c B E S (remq1 d D) Y N G T)))
      (else c))))

(define cycle
  (lambdag@ (c)
    (let loop ((c^ c)
               (fns^ (LOF))
               (n (length (LOF))))
      (cond
        ((zero? n) c^)
        ((null? fns^) (loop c^ (LOF) n))
        (else
         (let ((c^^ ((car fns^) c^)))
           (cond
             ((not (eq? c^^ c^))                                    
              (loop c^^ (cdr fns^) (length (LOF))))
             (else (loop c^ (cdr fns^) (- n 1))))))))))

(define absento
  (lambda (u v)
    (lambdag@ (c : B E S D Y N G T)
      (cond
        [(mem-check u v S) (mzero)]
        [else (unit (make-c B E S D Y N G `((,u . ,v) . ,T)))]))))

(define eigen-absento
  (lambda (e* x*)
    (lambdag@ (c : B E S D Y N G T)
      (cond
        [(eigen-occurs-check e* x* S) (mzero)]
        [else (unit (make-c B `((,e* . ,x*) . ,E) S D Y N G T))]))))


(define mem-check
  (lambda (u t S)
    (let ((t (walk t S)))
      (cond
        ((pair? t)
         (or (term=? u t S)
             (mem-check u (car t) S)
             (mem-check u (cdr t) S)))
        (else (term=? u t S))))))

(define term=?
  (lambda (u t S)
    (cond
      ((unify u t S) =>
       (lambda (S0)
         (eq? S0 S)))
      (else #f))))

(define ground-non-<type>?
  (lambda (pred)
    (lambda (u S)
      (let ((u (walk u S)))
        (cond
          ((var? u) #f)
          (else (not (pred u))))))))

;; moved 
(define ground-non-string?
  (ground-non-<type>? string?))

(define ground-non-symbol?
  (ground-non-<type>? symbol?))

(define ground-non-number?
  (ground-non-<type>? number?))

(define symbolo
  (lambda (u)
    (lambdag@ (c : B E S D Y N G T)
      (cond
        [(ground-non-symbol? u S) (mzero)]
        [(mem-check u N S) (mzero)]
        [(mem-check u G S) (mzero)]
        [else (unit (make-c B E S D `(,u . ,Y) N G T))]))))

(define stringo
  (lambda (u)
    (lambdag@ (c : B E S D Y N G T)
      (cond
        [(ground-non-string? u S) (mzero)]
        [(mem-check u N S) (mzero)]
        [(mem-check u Y S) (mzero)]
        [else (unit (make-c B E S D Y N `(,u . ,G) T))]))))

(define numbero 
  (lambda (u)
    (lambdag@ (c : B E S D Y N G T)
      (cond
        [(ground-non-number? u S) (mzero)]
        [(mem-check u Y S) (mzero)]
        [(mem-check u G S) (mzero)]
        [else (unit (make-c B E S D Y `(,u . ,N) G T))]))))

;; end moved

(define =/= ;; moved
  (lambda (u v)
    (lambdag@ (c : B E S D Y N G T)
      (cond
        ((unify u v S) =>
         (lambda (S0)
           (let ((pfx (prefix-S S0 S)))
             (cond
               ((null? pfx) (mzero))
               (else (unit (make-c B E S `(,pfx . ,D) Y N G T)))))))
        (else c)))))

(define ==
  (lambda (u v)
    (lambdag@ (c : B E S D Y N G T)
      (cond
        ((unify u v S) =>
         (lambda (S0)
           (cond
             ((==fail-check B E S0 D Y N G T) (mzero))
             (else (unit (make-c B E S0 D Y N G T))))))
        (else (mzero))))))

(define succeed (== #f #f))

(define fail (== #f #t))

(define ==fail-check
  (lambda (B E S0 D Y N G T)
    (cond
      ((eigen-absento-fail-check E S0) #t)
      ((atomic-fail-check S0 G ground-non-string?) #t)
      ((atomic-fail-check S0 Y ground-non-symbol?) #t)
      ((atomic-fail-check S0 N ground-non-number?) #t)
      ((symbolo-numbero-stringo-fail-check S0 Y N G) #t)
      ((=/=-fail-check S0 D) #t)
      ((absento-fail-check S0 T) #t)
      (else #f))))

(define eigen-absento-fail-check
  (lambda (E S0)
    (exists (lambda (e*/x*) (eigen-occurs-check (car e*/x*) (cdr e*/x*) S0)) E)))

(define atomic-fail-check
  (lambda (S A pred)
    (exists (lambda (a) (pred (walk a S) S)) A)))

(define symbolo-numbero-stringo-fail-check
  (lambda (S A N G)
    (let ((N (map (lambda (n) (walk n S)) N))
	  (G (map (lambda (g) (walk g S)) G)))
      (exists (lambda (a)
		 (let ([a (walk a S)])
		    (or (exists (same-var? a) N)
			(exists (same-var? a) G)
			)))
        A))))

(define absento-fail-check
  (lambda (S T)
    (exists (lambda (t) (mem-check (lhs t) (rhs t) S)) T)))

(define =/=-fail-check
  (lambda (S D)
    (exists (d-fail-check S) D)))

(define d-fail-check
  (lambda (S)
    (lambda (d)
      (cond
        ((unify* d S) =>
	 (lambda (S+) (eq? S+ S)))
        (else #f)))))

(define reify
  (lambda (x)
    (lambda (c)
      (let ((c (cycle c)))
        (let* ((S (c->S c))
             (D (walk* (c->D c) S))
             (Y (walk* (c->Y c) S))
             (N (walk* (c->N c) S))
	     (G (walk* (c->G c) S))
             (T (walk* (c->T c) S)))
        (let ((v (walk* x S)))
          (let ((R (reify-S v '())))
            (reify+ v R
                    (let ((D (remp
                              (lambda (d)
                                (let ((dw (walk* d S)))
                                  (or
                                    (anyvar? dw R)
                                    (anyeigen? dw R))))
                               (rem-xx-from-d D S))))
                      (rem-subsumed D)) 
                    (remp
                     (lambda (y) (var? (walk y R)))
                     Y)
                    (remp
                     (lambda (n) (var? (walk n R)))
                     N)
                    (remp
                     (lambda (g) (var? (walk g R)))
                     G)
                    (remp (lambda (t)
                            (or (anyeigen? t R) (anyvar? t R))) T)))))))))

(define reify+
  (lambda (v R D Y N G T)
    (form (walk* v R)
          (walk* D R)
          (walk* Y R)
          (walk* N R)
          (walk* G R)
          (rem-subsumed-T (walk* T R)))))

(define form
  (lambda (v D Y N G T)
    (let ((fd (sort-D D))
          (fy (sorter Y))
          (fn (sorter N))
          (fg (sorter G))	  
          (ft (sorter T)))
      (let ((fd (if (null? fd) fd
                    (let ((fd (drop-dot-D fd)))
                      `((=/= . ,fd)))))
            (fy (if (null? fy) fy `((sym . ,fy))))
            (fn (if (null? fn) fn `((num . ,fn))))
            (fg (if (null? fg) fg `((str . ,fg))))
            (ft (if (null? ft) ft
                    (let ((ft (drop-dot ft)))
                      `((absento . ,ft))))))
        (cond
          ((and (null? fd) (null? fy)
                (null? fn) (null? ft))
           v)
          (else (append `(,v) fd fn fy ft)))))))

(define sort-D
  (lambda (D)
    (sorter
     (map sort-d D))))

(define sort-d
  (lambda (d)
    (sort
       (lambda (x y)
         (lex<=? (car x) (car y)))
       (map sort-pr d))))

(define drop-dot-D
  (lambda (D)
    (map drop-dot D)))

(define lex<-reified-name?
  (lambda (r)
    (char<?
     (string-ref
      (datum->string r) 0)
     #\_)))

(define sort-pr
  (lambda (pr)
    (let ((l (lhs pr))
          (r (rhs pr)))
      (cond
        ((lex<-reified-name? r) pr)
        ((lex<=? r l) `(,r . ,l))
        (else pr)))))

(define rem-subsumed
  (lambda (D)
    (let rem-subsumed ((D D) (d^* '()))
      (cond
        ((null? D) d^*)
        ((or (subsumed? (car D) (cdr D))
             (subsumed? (car D) d^*))
         (rem-subsumed (cdr D) d^*))
        (else (rem-subsumed (cdr D)
                (cons (car D) d^*)))))))
 
(define subsumed?
  (lambda (d d*)
    (cond
      ((null? d*) #f)
      (else
        (let ((d^ (unify* (car d*) d)))
          (or
            (and d^ (eq? d^ d))
            (subsumed? d (cdr d*))))))))

(define rem-xx-from-d
  (lambda (D S)
    (remp not
          (map (lambda (d)
                 (cond
                   ((unify* d S) =>
                    (lambda (S0)
                      (prefix-S S0 S)))
                   (else #f)))
               D))))

(define rem-subsumed-T 
  (lambda (T)
    (let rem-subsumed ((T T) (T^ '()))
      (cond
        ((null? T) T^)
        (else
         (let ((lit (lhs (car T)))
               (big (rhs (car T))))
           (cond
             ((or (subsumed-T? lit big (cdr T))
                  (subsumed-T? lit big T^))
              (rem-subsumed (cdr T) T^))
             (else (rem-subsumed (cdr T)
                     (cons (car T) T^))))))))))

(define subsumed-T? 
  (lambda (lit big T)
    (cond
      ((null? T) #f)
      (else
       (let ((lit^ (lhs (car T)))
             (big^ (rhs (car T))))
         (or
           (and (eq? big big^) (member* lit^ lit))
           (subsumed-T? lit big (cdr T))))))))

(define LOF
  (lambda ()
    `(,drop-N-b/c-const ,drop-Y-b/c-const ,drop-Y-b/c-dup-var
      ,drop-N-b/c-dup-var ,drop-D-b/c-Y-or-N ,drop-T-b/c-Y-and-N
      ,move-T-to-D-b/c-t2-atom ,split-t-move-to-d-b/c-pair
      ,drop-from-D-b/c-T ,drop-t-b/c-t2-occurs-t1)))

;;;;;
(define booleano
  (lambda (x)
    (conde
      ((== #f x))
      ((== #t x)))))
(define onceo (lambda (g) (condu (g))))
;; define else as an alias for succeed
;; this permits more idiomatic scheme usage in conde
(define else succeed)
