(module test
   (library bkanren)
   (main main))

(define (main args)
   (print (run* (q)
	     (== #t q)))
   
   (print (run* (q)
   	     (fresh (x)
   		(== #t x)
   		(== x q))))

   (print (run* (x)
   	     (conde ((== 'olive x) succeed)
   		    ((== 'oil x) succeed)
   		    (else fail))))

   (print (run* (r)
   	     (fresh (x y)
   		(caro '(grape raisin pear) x)
   		(caro '((a) (b) (c)) y)
   		(== (cons x y) r))))


   (print (run 1 (q)
   	     alwayso
   	     (== #t q)))


   (print (run 1 (q)
   	     (== #f q)
   	     (== #t q)))

   ;;; why does this work
   (print (run 5 (q)
   	     (conde ((== #f q) alwayso)
   		((== #t q) alwayso)
   		(else fail))
   	     (== #t q)))
 
   )


