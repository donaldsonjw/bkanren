;; show that tabled miniKanren relations can solve the left-recursion elimination.
;; the grammar can be either CFG or Left-regular and is encoded using Prolog's DCGs
;; based on the difference list technique (code was originally auto-generated).
;;
;; If the top-level goal (X) is not tabled then the program diverges (under both
;; the interpreter and the compiler, obviously). We are using Bigloo 4.1a on 64-bit Ubuntu here.
;;
;; Peter Kourzanov

(module Parse-memo
   (library bkanren srfi1)
)

(define-syntax verify (syntax-rules (=== == = => ==> ===> -> --> ---> := :->)
 ([_ name term = data] (verify name term [=] data))
 ([_ name term := data] (verify name term [eq?] data))
 ([_ name term == data] (verify name term [eqv?] data))
 ([_ name term === data] (verify name term [equal?] data))
 ; :=> doesn't make sense with 'data (which is always a list)
 ([_ name term => . data] (verify name term [eq?] 'data))
 ([_ name term ==> . data] (verify name term [eqv?] 'data))
 ([_ name term ===> . data] (verify name term [equal?] 'data))
 ([_ name term -> . data] (verify name term [lset= =] 'data))
 ([_ name term :-> . data] (verify name term [lset= eq?] 'data))
 ([_ name term --> . data] (verify name term [lset= eqv?] 'data))
 ([_ name term ---> . data] (verify name term [lset= equal?] 'data))
 ([_ name term (eq args ...) data]
   (let ([result term]
	 [expected data])
      (if (eq args ... result expected)
	  (begin (printf "~a: passes OK~n" 'name)
		 `(passed: name))
	  (begin (printf "~a: expected ~s found ~s~n" 'name data result)
		 (error 'name "is" "failing")
		 (exit)
		 )
	  )))
 ))

;; some preliminaries...

;; tabled [[appendo]]
(define tappendo (tabled (a b c)
   (tconde
    ([t== a '()] (t== b c))
    (tsucceed (exist (x a1 c1)
	(t== a `(,x . ,a1))
	(t== c `(,x . ,c1))
	(tappendo a1 b c1)))
    ))
   )

(trun* (q) (tappendo '(a b) '(c) q))
(trun* (q) (tappendo '(a b) q '(a b c)))
(trun* (q) (tappendo q '(c) '(a b c)))
(trun* (q) (exist (x y) (tappendo x y '(a b c)) (t== q `(,x ,y))))
(trun 2 (q) (exist (x y) (tappendo x '(c) y) (t== q `(,x ,y))))
(trun* (q) (exist (x y) (tappendo '(a b) x y) (t== q `(,x ,y))))


;; our test grammar (can be CFG, but now is Left-regular)
;; X=z|X a
;; uncomment the (t== Lin (cons 'b temp)) below to make it
;; X=z|b X a
;; the output of the goal is a Peano representation of n in:
;; X=L={b^n a^n|n>=0}

(define head_75
  (lambda (Lin Lout var)
        (tall
	   (t== var 'z)
	   (t== Lin Lout)
	   )
       ))
     

(define head_77
  (lambda (Lin Lout var)
       (exist (x temp temp1)
	  (t== var (list 'S x))
	  ; although this could be CFG, can show left-recursion problem
	  ; with a left-regular language too (therefore, don't match 'b)
	  (t== Lin temp)
	  ;(t== Lin (cons 'b temp))
	  (X temp temp1 x)
	  (t== temp1 (cons 'a Lout))
	  )
       ))


(define X
;; exchange [[lambda]] for [[tabled]] to see divergence
  (tabled args
       (tconde (tfail)
              ((apply head_75 args))
              ((apply head_77 args))
	      )
       ))


;; swap these branches if you exchanged CFG <=> Left-regular
(if #f (begin
(verify SS.zero (trun* (q) (X '() '() q)) ===> z)
(verify SS.fwd1 (trun* (q) (X '(b a) '() q)) ===> (S z))
(verify SS.fwd2 (trun* (q) (X '(b b a a) '() q)) ===> (S (S z)))
(verify SS.prefix (trun* (q) (exist (_ r) (X '(b b b a a a) _ r) (t== q `(,_ ,r)))) --->
   ((b b b a a a) z)
   (() (S (S (S z))))
   )
(verify SS.rev0 (trun* (q) (X q '() 'z)) ===> ())
(verify SS.rev1 (trun* (q) (X q '() '(S z))) ===> (b a))
(verify SS.rev2 (trun* (q) (X q '() '(S (S z)))) ===> (b b a a))
(verify SS.fail (trun* (q) (X '(a) '() q)) =>)
(verify SS.fail (trun* (q) (X '(a a) '() q)) =>)
(verify SS.fail (trun* (q) (X '(a a a) '() q)) =>)
(verify SS.fail (trun* (q) (X q '() 'x)) =>)
(verify SS.fail (trun* (q) (X q '() '(S x))) =>)
(verify SS.fail (trun* (q) (X q '() '(S (S x)))) =>)
(verify SS.enum (trun 3 (q) (exist (x y) (X x '() y) (t== q `(,x ,y)))) --->
   (() z)
   ((b a) (S z))
   ((b b a a) (S (S z)))
   )
)
(begin
(verify SS.zero (trun* (q) (X '() '() q)) ===> z)
(verify SS.fwd (trun* (q) (X '(a a) '() q)) ===> (S (S z)))
(verify SS.prefix (trun* (q) (exist (_ r) (X '(a a a a) _ r) (t== q `(,_ ,r)))) --->
   ((a a a a) z)
   ((a a a) (S z))
   ((a a) (S (S z)))
   ((a) (S (S (S z))))
   (() (S (S (S (S z))))))
   
(verify SS.fwd (trun* (q) (X '(a a a a) '() q)) ===> (S (S (S (S z)))))
(verify SS.fwd (trun* (q) (X '(a a a a a a) '() q)) ===> (S (S (S (S (S (S z)))))))
(verify SS.rev0 (trun* (q) (X q '() 'z)) ===> ())
(verify SS.rev1 (trun* (q) (X q '() '(S z))) ===> (a))
(verify SS.rev2 (trun* (q) (X q '() '(S (S z)))) ===> (a a))
(verify SS.fail (trun* (q) (X '(a) '() q)) ===> (S z))
(verify SS.fail (trun* (q) (X '(a a a) '() q)) ===> (S (S (S z))))
(verify SS.fail (trun* (q) (X '(a a a a a) '() q)) ===> (S (S (S (S (S z))))))
(verify SS.fail (trun* (q) (X q '() 'x)) =>)
(verify SS.fail (trun* (q) (X q '() '(S x))) =>)
(verify SS.fail (trun* (q) (X q '() '(S (S x)))) =>)
(verify SS.enum (trun 3 (q) (exist (x y) (X x '() y) (t== q `(,x ,y)))) ---> (() z) ((a) (S z)) ((a a) (S (S z))))
))
