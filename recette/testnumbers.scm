; begin
(module testnumbers
   (library bkanren); srfi1)
   (main main)
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


(define (main args)
  (verify "sums"
  (run 5 (q)
    (fresh (x y z)
      (pluso x y z)
      (== `(,x ,y ,z) q))) ===>
    (_.0 () _.0)
    (() (_.0 . _.1) (_.0 . _.1))
    ((1) (1) (0 1))
    ((1) (0 _.0 . _.1) (1 _.0 . _.1))
    ((1) (1 1) (0 0 1)))

  (verify "factors"
  (run* (q)
    (fresh (x y)
      (*o x y (build-num 24))
      (== `(,x ,y ,(build-num 24)) q))) ===>
    ((1) (0 0 0 1 1) (0 0 0 1 1))
    ((0 0 0 1 1) (1) (0 0 0 1 1))
    ((0 1) (0 0 1 1) (0 0 0 1 1))
    ((0 0 1) (0 1 1) (0 0 0 1 1))
    ((0 0 0 1) (1 1) (0 0 0 1 1))
    ((1 1) (0 0 0 1) (0 0 0 1 1))
    ((0 1 1) (0 0 1) (0 0 0 1 1))
    ((0 0 1 1) (0 1) (0 0 0 1 1)))
)
; the end