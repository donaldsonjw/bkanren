(define-syntax trample
   (syntax-rules ()
      ((_ e) (lambda () e))))

(define-syntax trun
   (syntax-rules ()
      ((_ e (q) g g* ...)
       (let ((n e))
	  (unless (or (boolean? n) (and (integer? n) (exact? n) (positive? n)))
	     (error 'run "not an exact positive integer" n))
	  ((cond ((number? n) (take' n)) (n take+) (else take*))
	   (list
	      ((exist (q)
		  g g* ...
		  (lambda (s sk)
		     (sk ((treify reify-name) q s))))
	       empty-s
	       (lambda (a) `(#t . ,a)))))))))

(define-syntax trun*
   (syntax-rules ()
      ((_ (q) g g* ...)
       (trun #f (q) g g* ...))))

(define-syntax run+
   (syntax-rules ()
      ((_ (q) g g* ...)
       (trun #t (q) g g* ...))))

(define-syntax tconde
   (syntax-rules ()
      ((_ (g))
       (lambda (s sk)
	  (trample (g s sk))))
      ((_ (g g* ...))
       (lambda (s sk)
	  (trample
	     (g s
		(lambda (s)
		   (trample
		      ((tconde (g* ...)) s sk)))))))
      ((_  (g0 g0* ...) (g1 g1* ...) ...)
       (lambda (s sk)
	  `(#f
	      ,(trample ((tconde (g0 g0* ...)) s sk))
	      ,(trample ((tconde (g1 g1* ...)) s sk))
	      ...)))))

(define-syntax exist
   (syntax-rules ()
      ((_ (x ...) g g* ...)
       (lambda (s sk)
	  (trample
	     (let ((x (make-var s)) ...)
		((tconde (g g* ...)) s sk)))))))

(define-syntax tconv (syntax-rules ()
 ([_ body]
  (let-syntax-rule ([K (c e) terms]
     (let-syntax ([c tconde]
		  [e t==])
	. terms))
     (extract* (conde ==) body (K [] body))
     ))
 ))

(define-syntax tabled
   (syntax-rules ()
      ((_ (a ...) g g* ...)
       (let ((table '()))
	  (lambda (a ...)
	     (let ((argv `(,a ...)))
		(lambda (s sk)
		   (let ((key ((treify reify-name) argv s)))
		      (consume argv s sk
			 (cond ((assoc key table) => cdr)
			       (else (let ((data (make-data '() '() '())))
					(data-queue-set! data
					   `(,(trample
						 ((exist () g g* ...) s
								      (installing-sk argv data)))))
					(set! table `((,key . ,data) . ,table))
					data)))
			 ))))
	     )))))