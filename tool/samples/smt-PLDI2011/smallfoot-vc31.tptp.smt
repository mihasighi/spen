(set-logic QF_NOLL)

(declare-sort Sll_t 0)

(declare-fun f () (Field Sll_t Sll_t))

(define-fun ls ((?in Sll_t) (?out Sll_t)) Space
(tospace (or (= ?in ?out)
(exists ((?u Sll_t))
(tobool
(ssep (pto ?in (ref f ?u)) (ls ?u ?out)
))))))

(declare-fun nil () Sll_t)

(declare-fun x_emp () Sll_t)
(declare-fun y_emp () Sll_t)
(declare-fun z_emp () Sll_t)
(declare-fun t_emp () Sll_t)
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
(declare-fun alpha0 () SetLoc)
(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)
(declare-fun alpha3 () SetLoc)
(declare-fun alpha4 () SetLoc)
(declare-fun alpha5 () SetLoc)
(declare-fun alpha6 () SetLoc)
(assert
  (and 
    (= nil nil)
(distinct nil x1 )
(distinct nil x2 )
(distinct nil x3 )
(distinct nil x4 )
(distinct nil x5 )
(distinct nil x6 )
(distinct x1 x6 )
(distinct x2 x6 )
(distinct x3 x4 )
(distinct x3 x5 )
    (tobool  (ssep  (pto x1  (ref f x6 ) ) (ssep  (index alpha0 (ls x2 x1 )) (ssep  (pto x6  (ref f x2 ) )(ssep (pto x_emp (ref f y_emp)) (pto z_emp (ref f t_emp)))))))
  )
)
(assert
  (not
    (and (distinct x7 x6 )    (tobool  (ssep  (index alpha1 (ls x7 x6 )) (ssep  (pto x6  (ref f x7 ) )(ssep (pto x_emp (ref f y_emp)) (pto z_emp (ref f t_emp))))))
)  ))

(check-sat)
