
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
(declare-fun x22 () Sll_t)
(declare-fun x23 () Sll_t)
(declare-fun x24 () Sll_t)
(declare-fun x25 () Sll_t)
(declare-fun x26 () Sll_t)
(declare-fun x27 () Sll_t)
(declare-fun x28 () Sll_t)
(declare-fun x29 () Sll_t)
(declare-fun x30 () Sll_t)
(declare-fun x31 () Sll_t)
(declare-fun x32 () Sll_t)
(declare-fun x33 () Sll_t)
(declare-fun x34 () Sll_t)
(declare-fun x35 () Sll_t)
(declare-fun x36 () Sll_t)
(declare-fun x37 () Sll_t)
(declare-fun x38 () Sll_t)
(declare-fun x39 () Sll_t)
(declare-fun x40 () Sll_t)
(declare-fun x41 () Sll_t)
(declare-fun x42 () Sll_t)
(declare-fun x43 () Sll_t)
(declare-fun x44 () Sll_t)

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
(declare-fun alpha16 () SetLoc)
(declare-fun alpha17 () SetLoc)
(declare-fun alpha18 () SetLoc)
(declare-fun alpha19 () SetLoc)

(assert 
	(and (= nil nil) (distinct nil x1) (distinct nil x2) (distinct nil x3) (distinct x1 x2) (distinct x2 x3) (distinct nil x5) (distinct nil x6) (distinct nil x7) (distinct x5 x6) (distinct x6 x7) (distinct nil x9) (distinct nil x10) (distinct nil x11) (distinct x9 x10) (distinct x10 x11) (distinct nil x13) (distinct nil x14) (distinct nil x15) (distinct x13 x14) (distinct x14 x15) (distinct nil x17) (distinct nil x18) (distinct nil x19) (distinct x17 x18) (distinct x18 x19) (distinct nil x21) (distinct nil x22) (distinct nil x23) (distinct x21 x22) (distinct x22 x23) (distinct nil x25) (distinct nil x26) (distinct nil x27) (distinct x25 x26) (distinct x26 x27) (distinct nil x29) (distinct nil x30) (distinct nil x31) (distinct x29 x30) (distinct x30 x31) (distinct nil x33) (distinct nil x34) (distinct nil x35) (distinct x33 x34) (distinct x34 x35) (distinct nil x37) (distinct nil x38) (distinct nil x39) (distinct x37 x38) (distinct x38 x39) 
	(tobool 
	(ssep 
		(index alpha0 (ls x39 x37 )) 
		(pto x37 (ref next x39) ) 
		(index alpha1 (ls x35 x33 )) 
		(pto x33 (ref next x35) ) 
		(index alpha2 (ls x31 x29 )) 
		(pto x29 (ref next x31) ) 
		(index alpha3 (ls x27 x25 )) 
		(pto x25 (ref next x27) ) 
		(index alpha4 (ls x23 x21 )) 
		(pto x21 (ref next x23) ) 
		(index alpha5 (ls x19 x17 )) 
		(pto x17 (ref next x19) ) 
		(index alpha6 (ls x15 x13 )) 
		(pto x13 (ref next x15) ) 
		(index alpha7 (ls x11 x9 )) 
		(pto x9 (ref next x11) ) 
		(index alpha8 (ls x7 x5 )) 
		(pto x5 (ref next x7) ) 
		(index alpha9 (ls x3 x1 )) 
		(pto x1 (ref next x3) ) 
	)

	)

	)

)

(assert (not 
	(tobool 
	(ssep 
		(index alpha10 (ls x40 x37 )) 
		(pto x37 (ref next x40) ) 
		(index alpha11 (ls x36 x33 )) 
		(pto x33 (ref next x36) ) 
		(index alpha12 (ls x32 x29 )) 
		(pto x29 (ref next x32) ) 
		(index alpha13 (ls x28 x25 )) 
		(pto x25 (ref next x28) ) 
		(index alpha14 (ls x24 x21 )) 
		(pto x21 (ref next x24) ) 
		(index alpha15 (ls x20 x17 )) 
		(pto x17 (ref next x20) ) 
		(index alpha16 (ls x16 x13 )) 
		(pto x13 (ref next x16) ) 
		(index alpha17 (ls x12 x9 )) 
		(pto x9 (ref next x12) ) 
		(index alpha18 (ls x8 x5 )) 
		(pto x5 (ref next x8) ) 
		(index alpha19 (ls x4 x1 )) 
		(pto x1 (ref next x4) ) 
	)

	)

))

(check-sat)
