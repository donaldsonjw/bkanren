(module bkanren-ext
   (include "mk.sch")
   (import bkanren)
   (export caro
	   cdro
	   conso
	   nullo
	   eqo
	   pairo
	   listo
	   lolo
	   twinso
	   listofo
	   loto
	   membero
	   eq-caro
	   memo
	   rembero
	   appendᵒ
	   unwrapo
	   swappendo
	   flatteno
	   flattenrevo
	   anyo
	   nevero
	   alwayso
	   salo
   ))


(define caro (lambda (p a)
		(fresh (d)
		   (== (cons a d) p))))

(define cdro (lambda (p d)
		(fresh (a)
		   (== (cons a d) p))))

(define conso (lambda (a d p)
		 (== (cons a d) p)))

(define nullo (lambda (x)
		 (== '() x)))

(define eqo (lambda (x y)
	       (== x y)))

(define pairo (lambda (p)
		 (fresh (a d)
		    (conso a d p))))

(define listo (lambda (l)
		 (conde
		    ((nullo l) succeed)
		    ((pairo l)
		     (fresh (d)
			(cdro l d)
			(listo d)))
		    (else fail))))

(define lolo (lambda (l)
		(conde
		   ((nullo l) succeed)
		   ((fresh (a)
		       (caro l a)
		       (listo a))
		    (fresh (d)
		       (cdro l d)
		       (lolo d)))
		   (else fail))))


(define twinso (lambda (s)
		  (fresh (x y)
		     (conso x y s)
		     (conso x '() y))))


(define listofo (lambda (predo l)
   (conde ((nullo l) succeed)
          ((fresh (a)
	      (caro l a)
	      (predo a))
	   (fresh (d)
	      (cdro l d)
	      (listofo predo d)))
	  (else fail))))


(define loto (lambda (l)
		(listofo twinso l)))


(define eq-caro (lambda (l x)
		   (caro l x)))

(define membero (lambda (x l)
   (conde ((nullo l) fail)
      ((eq-caro l x) succeed)
      (else
       (fresh (d)
	  (cdro l d)
	  (membero x d))))))

(define memo (lambda (x l out)
		(conde ((eq-caro l x)
			(== l out))
		       (else
			(fresh (d)
			   (cdro l d)
			   (memo x d out))))))

(define rembero (lambda (x l out)
		   (conde ((nullo l) (== '() out))
		      ((eq-caro l x) (cdro l out))
		      (else
		       (fresh (res)
			  (fresh (d)
			     (cdro l d)
			     (rembero x d res))
			  (fresh (a)
			     (caro l a)
			     (conso a res out)))))))


(define appendᵒ (lambda (l s out)
		   (conde ((nullo l) (== s out))
		      (else
		       (fresh (a d res)
			  (conso a d l)
			  (conso a res out)
			  (appendᵒ d s res))))))


(define swappendo (lambda (l s out)
		     (conde (succeed
			       (fresh (a d res)
				  (conso a d l)
				  (conso a res out)
				  (swappendo d s res)))
			(else (nullo l) (== s out)))))

		     
(define unwrapo (lambda (x out)
		   (conde (succeed (== x out))
		      ((pairo x)
		       (fresh (a)
			  (caro x a)
			  (unwrapo a out))))))

(define flatteno (lambda (s out)
   (conde ((nullo s) (== '() out))
      ((pairo s)
       (fresh (a d res-a res-d)
	  (conso a d s)
	  (flatteno a res-a)
	  (flatteno d res-d)
	  (appendᵒ res-a res-d out)))
      (else
       (conso s '() out)))))

(define flattenrevo (lambda (s out)
		       (conde (succeed (conso s '() out))
			  ((nullo s) (== '() out))
			  (else
			   (fresh (a d res-a res-d)
			      (flattenrevo a res-a)
			      (flattenrevo d res-d)
			      (appendᵒ res-a res-d out))))))

(define anyo (lambda (g)
		(conde (g succeed)
		   (else (anyo g)))))

(define nevero (anyo fail))

(define alwayso (anyo succeed))

(define salo (lambda (g)
		(conde (succeed succeed)
		   (else g))))

