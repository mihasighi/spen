
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
(declare-fun x5 () Sll_t)
(declare-fun x6 () Sll_t)
(declare-fun x7 () Sll_t)
(declare-fun x8 () Sll_t)
(declare-fun x9 () Sll_t)
(declare-fun x10 () Sll_t)
(declare-fun x11 () Sll_t)
(declare-fun x12 () Sll_t)
(declare-fun x13 () Sll_t)
(declare-fun x14 () Sll_t)
(declare-fun x15 () Sll_t)
(declare-fun x16 () Sll_t)
(declare-fun x17 () Sll_t)
(declare-fun x18 () Sll_t)
(declare-fun x19 () Sll_t)
(declare-fun x20 () Sll_t)
(declare-fun x21 () Sll_t)

;; declare set of locations

(declare-fun alpha0 () SetLoc)
(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)
(declare-fun alpha3 () SetLoc)
(declare-fun alpha4 () SetLoc)
(declare-fun alpha5 () SetLoc)
(declare-fun alpha6 () SetLoc)
(declare-fun alpha7 () SetLoc)
(declare-fun alpha8 () SetLoc)
(declare-fun alpha9 () SetLoc)
(declare-fun alpha10 () SetLoc)
(declare-fun alpha11 () SetLoc)
(declare-fun alpha12 () SetLoc)
(declare-fun alpha13 () SetLoc)
(declare-fun alpha14 () SetLoc)
(declare-fun alpha15 () SetLoc)

(assert 
	(and (= nil nil) (distinct x6 x17) (distinct x3 x5) (distinct x7 x17) (distinct x7 x14) (distinct x2 x12) (distinct x4 x6) (distinct x4 x9) (distinct x4 x13) (distinct x4 x17) (distinct x1 x11) (distinct x1 x16) (distinct x1 x13) (distinct x1 x14) (distinct x13 x14) (distinct x16 x17) (distinct x5 x6) 
	(tobool 
	(ssep 
		(index alpha0 (ls x5 x2 )) 
		(index alpha1 (ls x10 x11 )) 
		(index alpha2 (ls x10 x4 )) 
		(index alpha3 (ls x13 x17 )) 
		(index alpha4 (ls x4 x5 )) 
		(index alpha5 (ls x8 x1 )) 
		(index alpha6 (ls x14 x3 )) 
		(index alpha7 (ls x17 x5 )) 
		(index alpha8 (ls x2 x3 )) 
		(index alpha9 (ls x9 x17 )) 
		(index alpha10 (ls x9 x12 )) 
		(index alpha11 (ls x9 x10 )) 
		(index alpha12 (ls x9 x3 )) 
		(index alpha13 (ls x3 x9 )) 
		(index alpha14 (ls x6 x12 )) 
		(index alpha15 (ls x6 x10 )) 
	)

	)

	)

)

(check-sat)
