(module Parse-memo
   (library bkanren srfi1 slib)
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

;(exit)

(define head_75
  (lambda (Lin Lout var)
        (tall
	   (t== var 'z)
	   (t== Lin Lout)
	   )
       ))
     

(define head_77
  (lambda (Lin Lout var)
       (exist (x temp)
	  (t== var (list 'S x))
	  (X Lin temp x)
	  (t== temp (cons 'a Lout))
	  )
       ))


(define X
  (tabled args
       (tconde (tfail)
              ((apply head_75 args))
              ((apply head_77 args))
	      )
       ))


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
;(exit)

(verify SS.rev2 (trun* (q) (X q '() '(S (S z)))) ===> (a a))
(verify SS.fail (trun* (q) (X '(a) '() q)) ===> (S z))
(verify SS.fail (trun* (q) (X '(a a a) '() q)) ===> (S (S (S z))))
(verify SS.fail (trun* (q) (X '(a a a a a) '() q)) ===> (S (S (S (S (S z))))))
(verify SS.fail (trun* (q) (X q '() 'x)) =>)
(verify SS.fail (trun* (q) (X q '() '(S x))) =>)
(verify SS.fail (trun* (q) (X q '() '(S (S x)))) =>)

;(exit)

(verify SS.enum (trun 3 (q) (exist (x y) (X x '() y) (t== q `(,x ,y)))) ---> (() z) ((a) (S z)) ((a a) (S (S z))))
