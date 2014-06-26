
(set-logic QF_S)

;; declare sorts
(declare-sort Sll_t 0)


;; declare fields
(declare-fun next () (Field Sll_t Sll_t))


;; declare predicates

(define-fun ls ((?in Sll_t) (?out Sll_t) ) Space (tospace 
	(or 
	(and (= ?in ?out) 
		(tobool emp
		)

	)
 
	(exists ((?u Sll_t) ) 
	(and (distinct ?in ?out) 
		(tobool (ssep 
		(pto ?in (ref next ?u) ) 
		(ls ?u ?out )
		) )

	)
 
	)

	)
))

;; declare variables
(declare-fun x0 () Sll_t)
(declare-fun x1 () Sll_t)
(declare-fun x2 () Sll_t)
(declare-fun x3 () Sll_t)
(declare-fun x4 () Sll_t)
(declare-fun const_0 () Sll_t)
(declare-fun const_1 () Sll_t)
(declare-fun const_2 () Sll_t)
(declare-fun const_3 () Sll_t)
(declare-fun const_4 () Sll_t)

;; declare set of locations


(assert 
	(and (= nil nil) 
	(tobool emp)

	)

)

(assert (not 
	(and (= nil nil) (= const_1 const_1) 
	(tobool emp)

	)

))

(check-sat)
