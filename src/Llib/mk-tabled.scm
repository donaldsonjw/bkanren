(module bkanren-tabled
   (include "mk.sch")
   (include "mk-tabled.sch")
   (import bkanren)
   (export
      take* take+ take'
      empty-s
      make-var
      reify-name treify
      t==
      consume
      make-data data-queue-set!
      installing-sk
   ))

(define-record-type data
   (make-data queue answers resumers)
   data?
   (queue data-queue data-queue-set!)
   (answers data-answers data-answers-set!)
   (resumers data-resumers data-resumers-set!))

(define (add-answer! data ansv)
    (data-answers-set! data `(,ansv . ,(data-answers data)))
    ;(printf "~nadded answer~n~a~n" data)
    )

(define (add-resumer! data k)
    (data-resumers-set! data `(,k . ,(data-resumers data)))
    ;(printf "~nadded resumer~n~a~n" data)
    )

(define-record-type var
   (make-var s)
   var?
   (s var-s))

(define reify-name
   (lambda (n) (string->symbol (string-append "_." (number->string n)))))

(define reify-var
   (lambda (s)
      (lambda (n) (make-var s))))



(define fail '())

(define subunify
   (lambda (arg ans s)
      (let ((arg (stored-shrink-walk arg s)))
	 (cond
	    ((eq? arg ans) s)
	    ((var? arg) (ext-s-no-check arg ans s))
	    ((pair? arg) (subunify (cdr arg) (cdr ans)
			    (subunify (car arg) (car ans) s)))
	    (else s)))))

(define reuse
   (lambda (argv ansv s)
      (subunify argv ((treify (reify-var s)) ansv s) s)))

(define subsumed
   (lambda (arg ans s)
      (let ((arg (stored-shrink-walk arg s))
            (ans (stored-shrink-walk ans s)))
	 (cond
	    ((eq? arg ans) s)
	    ((var? ans) (ext-s ans arg s))
	    ((and (pair? arg) (pair? ans))
	     (let ((s (subsumed (car arg) (car ans) s)))
		(and s (subsumed (cdr arg) (cdr ans) s))))
	    ((equal? arg ans) s)
	    (else #f)))))

(define master
   (lambda (data argv)
      (let ((queue (data-queue data)))
	 (cond
	    ((null? queue) fail)
	    (else
	     (data-queue-set! data '())
	     `((,(lambda (queue) (data-queue-set! data queue))
                . ,(trample (master data argv)))
	       . (,queue . ())))))))

(define consume
   (lambda (argv s sk data)
      (let ((resumer (lambda (ansv)
			(trample (sk (reuse argv ansv s))))))
	 (add-resumer! data resumer)
	 `(#f ,(master data argv)
	     . ,(map resumer (data-answers data))))))

(define installing-sk
   (lambda (argv data)
      (lambda (s)
	 (if (any (lambda (ansv) (subsumed argv ansv s))
		(data-answers data))
	     fail
	     (let ((ansv ((treify (reify-var s)) argv s)))
		(add-answer! data ansv)
		`(#f . ,(map (lambda (k) (k ansv)) (data-resumers data))))))))


(define empty-s '())

(define t==
   (lambda (u v)
      (lambda (s sk)
	 (trample
	    (cond
	       ((unify u v s) => sk)
	       (else fail))))))

(define taker
   (lambda (queue sk fk)
      (if (null? queue) '()
	  (let ((th (car queue)) (queue (cdr queue)))
	     (cond
		((and (pair? th) (pair? (car th)))
		 (let ((finish! (caar th)) (old (cadr th))
					   (restart (cdar th)) (new (cddr th)))
		    (if (null? old)
			(let ((wen (reverse new)))
			   (finish! wen)
			   (if (null? wen)
			       (fk queue)
			       (fk `(,@queue ,restart))))
			(taker `(,(car old))
			   (lambda (a new+)
			      (sk a `((,(car th) . (,(cdr old) . (,@new+ . ,new))) . ,queue)))
			   (lambda (new+)
			      (fk `((,(car th) . (,(cdr old) . (,@new+ . ,new))) . ,queue)))))))
		((and (pair? th) (car th))
		 (sk (cdr th) queue))
		(else
		 (fk (cond
			((null? th) queue)
			((pair? th) `(,@(cdr th) . ,queue))
			(else `(,@queue ,(th)))))))))))

(define take'
   (lambda (n)
      (lambda (ths)
	 (if (zero? n) '()
	     (taker ths
		(lambda (a ths) `(,a . ,((take' (- n 1)) ths)))
		(take' n))))))

(define take*
   (lambda (ths)
      (taker ths
	 (lambda (a ths) `(,a . ,(take* ths)))
	 take*)))

(define take+
   (lambda (ths)
      (taker ths
	 (lambda (a ths) `(,a . ,(lambda () (take+ ths))))
	 take+)))

(define stored-shrink-walk
   (lambda (v start)
      (let loop ((v v) (s start) (end '()))
	 (if (or (not (var? v))
		 (eq? s (var-s v))
		 (eq? s end))
	     v
	     (if (eq? (caar s) v)
		 (loop (cdar s) start (cdr s))
		 (loop v (cdr s) end))))))

(define shrink-walk
   (lambda (v start)
      (let loop ((v v) (s start) (end '()))
	 (if (or (not (var? v))
		 (eq? s end))
	     v
	     (if (eq? (caar s) v)
		 (loop (cdar s) start (cdr s))
		 (loop v (cdr s) end))))))

(define assq-walk ; not used
   (lambda (v s)
      (cond
	 ((and (var? v) (assq v s))
	  => (lambda (p) (assq-walk (cdr p) s)))
	 (else v))))

(define walk*
   (lambda (walk)
      (lambda (t s)
	 (let walk* ((t t))
	    (let ((t (walk t s)))
	       (if (pair? t)
		   (cons
		      (walk* (car t))
		      (walk* (cdr t)))
		   t))))))

(define treify
   (lambda (rep)
      (lambda (t s)
	 (let ((t ((walk* stored-shrink-walk) t s)))
	    (let ((s (reify-vars rep t)))
	       ((walk* shrink-walk) t s))))))

(define reify-vars
   (lambda (rep t)
      (let rec ((t t) (s '()))
	 (cond
	    ((and (var? t) (not (assq t s)))
	     (cons (cons t (rep (length s))) s))
	    ((pair? t) (rec (cdr t) (rec (car t) s)))
	    (else s)))))

(define occurs?
   (lambda (x t)
      (or (eq? x t)
	  (and (pair? t)
	       (or
		(occurs? x (car t))
		(occurs? x (cdr t)))))))

(define ext-s-no-check
   (lambda (x v s)
      (cons (cons x v) s)))

(define ext-s-check
   (lambda (x v s)
      (and (not (occurs? x v))
	   (ext-s-no-check x v s))))

(define ext-s ext-s-check)

(define occurs-check
   (let ((f #t))
      (lambda args
	 (cond ([null? args] f)
	       ((and [list? args] [car args]) => (lambda (b)
		(unless (boolean? b) (error 'occurs-check "not a boolean" b))
		(set! f b) (set! ext-s (if f ext-s-check ext-s-no-check))
		))
	       ))
      ))

(define unify
   (lambda (v w s)
      (let ((v (stored-shrink-walk v s))
            (w (stored-shrink-walk w s)))
	 (cond
	    ((eq? v w) s)
	    ((var? v) (ext-s v w s))
	    ((var? w) (ext-s w v s))
	    ((and (pair? v) (pair? w))
	     (let ((s (unify (car v) (car w) s)))
		(and s (unify (cdr v) (cdr w) s))))
	    ((equal? v w) s)
	    (else #f)))))
