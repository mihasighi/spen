
; Extending QF_S:
; constant emptybag, 
; the function bag, 
; the multiset comparison operator bag-lt, bag-le, bag-gt, bag-ge
; bagunion, bag-diff, bag-sub

(set-logic QF_SLRDI)

;; declare sorts
(declare-sort Rbt_t 0)

;; declare fields
(declare-fun left () (Field Rbt_t Rbt_t))
(declare-fun right () (Field Rbt_t Rbt_t))
(declare-fun data () (Field Rbt_t Int))
(declare-fun color () (Field Rbt_t Int))

;; declare predicates

;; Each node has two data fields: data, color (0: red, 1: black). 
;; the rbt predicate defined here does not require the root to be black

;; rbt(E, M, N, C)::= E = nil & emp & M = emptyset & N = 1 & C = 1 | 
;; exists X,Y,M1,M2,N1,N2,C1,C2. E |-> ((left,X), (right,Y)) * rbt(X,M1,N1,C1) * rbt(Y,M2,N2,C2) & M = {E.data} cup M1 cup M2 & 
;; M1 < E.data < M2 & N1 = N2 & C = E.color  & 0 <= C <= 1 & ite(C=0, N = N1, N=N1+1) & C = 0 => (C1 = 1 & C2 = 1)


(define-fun rbt ((?E Rbt_t) (?M BagInt) (?N Int) (?C Int)) Space (tospace 
	(or 
	(and (= ?E nil) 
		(tobool emp
		)
		(= ?M emptybag)
		(= ?N 1)
		(= ?C 1)
	)
 
	(exists ( (?X Rbt_t) (?Y Rbt_t) (?M1 BagInt) (?M2 BagInt) (?N1 Int) (?N2 Int) (?C1 Int) (?C2 Int) (?d Int) (?c Int) ) 
	(and (distinct ?E nil) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d) (ref color ?c) ) ) 
			(rbt ?X ?M1 ?N1 ?C1)
			(rbt ?Y ?M2 ?N2 ?C2)
		)
		)
		(= ?M (bagunion ?M1 (bag ?d) ?M2) )
		(< ?M1 (bag ?d))
		(< (bag ?d) ?M2)
		(= ?N (ite (= ?C 0) ?N1 (+ ?N1 1) ) )
		(= ?N1 ?N2)
		(= ?c ?C)	
		(= ?C 0) (= ?C1 1) (= ?C2 1)
	)
	)

	(exists ( (?X Rbt_t) (?Y Rbt_t) (?M1 BagInt) (?M2 BagInt) (?N1 Int) (?N2 Int) (?C1 Int) (?C2 Int) (?d Int) (?c Int) ) 
	(and (distinct ?E nil) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d) (ref color ?c) ) ) 
			(rbt ?X ?M1 ?N1 ?C1)
			(rbt ?Y ?M2 ?N2 ?C2)
		)
		)
		(= ?M (bagunion ?M1 (bag ?d) ?M2) )
		(< ?M1 (bag ?d))
		(< (bag ?d) ?M2)
		(= ?N (ite (= ?C 0) ?N1 (+ ?N1 1) ) )
		(= ?N1 ?N2)
		(= ?c ?C)	
		(= ?C 1) (<= 0 ?C1) (<= ?C1 1) (<= 0 ?C2) (<= ?C2 1)
	)
	)
	)
))

;; rbthole(E,F, M1, N1, C1, M2, N2, C2)::= E = F & emp & M1 = M2 & N1 = N2 & C1 = C2 | 
;; exists X,Y,M3,M4,N3,N4, C3, C4. E |-> ((left,X), (right,Y)) * rbt(X,M3,N3,C3) * rbthole(Y,F,M4,N4,C4, M2, N2, C2) & 
;; M1 = {E.data} cup M3 cup M4 & M3 < E.data < M4 & N3 = N4 & C1 = E.color & 0 <= C1,C3,C4 <= 1 & ite(C1=0, N1=N3, N1=N3+1) & 
;; C1 = 0 => (C3 = 1 & C4 = 1) |
;; exists X,Y,M3,M4,N3,N4, C3, C4. E |-> ((left,X), (right,Y)) * rbthole(X,F,M3,N3,C3, M2, N2, C2) * rbt(Y,M4,N4,C4) & 
;; M1 = {E.data} cup M3 cup M4 & M3 < E.data < M4 & N3 = N4 & C1 = E.color & 0 <= C1,C3,C4 <= 1 & ite(C1=0, N1=N3, N2=N3+1) & 
;; C1 = 0 => (C3 = 1 & C4 = 1)

(define-fun rbthole ((?E Rbt_t) (?F Rbt_t) (?M1 BagInt) (?N1 Int) (?C1 Int) (?M2 BagInt) (?N2 Int) (?C2 Int)) Space (tospace 
	(or 
	(and (= ?E ?F) 
		(tobool emp
		)
		(= ?M1 ?M2)
		(= ?N1 ?N2)
		(= ?C1 ?C2)
	)
 
	(exists ( (?X Rbt_t) (?Y Rbt_t) (?M3 BagInt) (?N3 Int) (?C3 Int) (?M4 BagInt) (?N4 Int) (?C4 Int) (?d Int) (?c Int) ) 
	(and (distinct ?E ?F) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d) (ref color ?c)) ) 
			(rbthole ?X ?F ?M3 ?N3 ?C3 ?M2 ?N2 ?C2)
			(rbt ?Y ?M4 ?N4 ?C4)
		)
		)
		(= ?M1 (bagunion ?M3 (bag ?d) ?M4) )
		(< ?M3 (bag ?d))
		(< (bag ?d) ?M4)
		(= ?N1 (ite (= ?C1 0) ?N3 (+ ?N3 1) ) )
		(= ?N3 ?N4)
		(= ?c ?C1)	
		(= ?C1 0) (= ?C3 1) (= ?C4 1)
	)
	)

	(exists ( (?X Rbt_t) (?Y Rbt_t) (?M3 BagInt) (?N3 Int) (?C3 Int) (?M4 BagInt) (?N4 Int) (?C4 Int) (?d Int) (?c Int) ) 
	(and (distinct ?E ?F) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d) (ref color ?c)) ) 
			(rbthole ?X ?F ?M3 ?N3 ?C3 ?M2 ?N2 ?C2)
			(rbt ?Y ?M4 ?N4 ?C4)
		)
		)
		(= ?M1 (bagunion ?M3 (bag ?d) ?M4) )
		(< ?M3 (bag ?d))
		(< (bag ?d) ?M4)
		(= ?N1 (ite (= ?C1 0) ?N3 (+ ?N3 1) ) )
		(= ?N3 ?N4)
		(= ?c ?C1)	
		(= ?C1 1) (<= 0 ?C3) (<= ?C3 1) (<= 0 ?C4) (<= ?C4 1)
	)
	)

	(exists ( (?X Rbt_t) (?Y Rbt_t) (?M3 BagInt) (?N3 Int) (?C3 Int) (?M4 BagInt) (?N4 Int) (?C4 Int) (?d Int) (?c Int) ) 
	(and (distinct ?E ?F) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d) (ref color ?c)) ) 
			(rbt ?X ?M3 ?N3 ?C3)
			(rbthole ?Y ?F ?M4 ?N4 ?C4 ?M2 ?N2 ?C2)
		)
		)
		(= ?M1 (bagunion ?M3 (bag ?d) ?M4) )
		(< ?M3 (bag ?d))
		(< (bag ?d) ?M4)
		(= ?N1 (ite (= ?C1 0) ?N3 (+ ?N3 1) ) )
		(= ?N3 ?N4)
		(= ?c ?C1)	
		(= ?C1 0) (= ?C3 1)(= ?C4 1)
	)
	)

	(exists ( (?X Rbt_t) (?Y Rbt_t) (?M3 BagInt) (?N3 Int) (?C3 Int) (?M4 BagInt) (?N4 Int) (?C4 Int) (?d Int) (?c Int) ) 
	(and (distinct ?E ?F) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d) (ref color ?c)) ) 
			(rbt ?X ?M3 ?N3 ?C3)
			(rbthole ?Y ?F ?M4 ?N4 ?C4 ?M2 ?N2 ?C2)
		)
		)
		(= ?M1 (bagunion ?M3 (bag ?d) ?M4) )
		(< ?M3 (bag ?d))
		(< (bag ?d) ?M4)
		(= ?N1 (ite (= ?C1 0) ?N3 (+ ?N3 1) ) )
		(= ?N3 ?N4)
		(= ?c ?C1)	
		(= ?C1 1) (<= 0 ?C3) (<= ?C3 1) (<= 0 ?C4) (<= ?C4 1)
	)
	)
	)
))


;; rbthole with the property that the nodes on the path from E to F alternate between red and black, 
;; with the root black, and all the children of black nodes are red nodes

;; brrbthole(E,F, M1, N1, C1, M2, N2, C2)::= E = F & emp & M1 = M2 & N1 = N2 & C1 = C2 | 
;; exists X,Y,U,V,M3,M4,M5,N3,N4,N5,C3,C4,C5. E |-> ((left,X), (right,Y)) * Y |->((left,U),(right,V)) * rbt(X,M3,N3,C3) * 
;; brrbthole(U,F,M4,N4,C4,M2,N2,C2) * rbt(V,M5,N5,C5) & M1 = {E.data} cup M3 cup {Y.data} cup M4 cup M5 & 
;; M3 < E.data < {Y.data} cup M4 cup M5 & M4 < Y.data < M5 & C1 = E.color & C1 = 1 & C3 = 0 & Y.color = 0 & C4 = 1 & N4 = N5 & 
;; N3 = N4 & N1 = N3 +1 | 
;; exists X,Y,U,V,M3,M4,M5,H3,H4,H5,C3,C4,C5. E |-> ((left,X), (right,Y)) * Y |->((left,U),(right,V)) * rbt(X,M3,N3,C3) * 
;; rbt(U,M4,N4,C4) * brrbthole(V,F,M5,N5,C5,M2,N2,C2) & M1 = {E.data} cup M3 cup {Y.data} cup M4 cup M5 & M3 < E.data < 
;; {Y.data} cup M4 cup M5 & M4 < Y.data < M5 & C1 = E.color & C1 = 1 & C3 = 0 & Y.color = 0 & C5 = 1 & N4 = N5 & N3 = N4 & N1 = N3 +1
;; | exists X,Y,U,V,M3,M4,M5,H3,H4,H5,C3,C4,C5. E |-> ((left,X), (right,Y)) * X |->((left,U),(right,V)) * rbt(U,M3,N3,C3) * 
;; brrbthole(V,F,M4,N4,C4,M2,N2,C2) * rbt(Y,M5,N5,C5) & M1 = {E.data} cup {X.data} cup M3 cup M4 cup M5 & {X.data} cup M3 cup M4 <
;; E.data < M5 & M3 < X.data < M4 & C1 = E.color & C1 = 1 & X.color = 0 & C5 = 0 & C4 = 1 & N3 = N4 & N3 = N5 & N1 = N5 +1 |
;; exists X,Y,U,V,M3,M4,M5,H3,H4,H5,C3,C4,C5. E |-> ((left,X), (right,Y)) * X |->((left,U),(right,V)) * 
;; brrbthole(U,F,M3,N3,C3, M2, N2, C2) * rbt(V,M4,N4,C4) * rbt(Y,M5,N5,C5) & M1 = {E.data} cup {X.data} cup M3 cup M4 cup M5 &
;; {X.data} cup M3 cup M4 < E.data < M5 & M3 < X.data < M4 & C1 = E.color & C1 = 1 & X.color = 0 & C5 = 0 & C3 = 1 & N3 = N4 & 
;; N3 = N5 & N1 = N5 +1

(define-fun brrbthole ((?E Rbt_t) (?F Rbt_t) (?M1 BagInt) (?N1 Int) (?C1 Int) (?M2 BagInt) (?N2 Int) (?C2 Int)) Space (tospace 
	(or 
	(and (= ?E ?F) 
		(tobool emp
		)
		(= ?M1 ?M2)
		(= ?N1 ?N2)
		(= ?C1 ?C2)
	)
 
	(exists ( (?X Rbt_t) (?Y Rbt_t) (?U Rbt_t) (?V Rbt_t) (?M3 BagInt) (?N3 Int) (?C3 Int) (?M4 BagInt) (?N4 Int) (?C4 Int)
		(?M5 BagInt) (?N5 Int) (?C5 Int) (?d1 Int) (?d2 Int) (?c1 Int) (?c2 Int) ) 
	(and (distinct ?E ?F) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d1) (ref color ?c1)) ) 
			(pto ?X (sref (ref left ?U) (ref right ?V) (ref data ?d2) (ref color ?c2)) )
			(brrbthole ?U ?F ?M3 ?N3 ?C3 ?M2 ?N2 ?C2)
			(rbt ?V ?M4 ?N4 ?C4) 
			(rbt ?Y ?M5 ?N5 ?C5)
		)
		)
		(= ?M1 (bagunion ?M3 (bag ?d2) ?M4 (bag ?d1) ?M5) )
		(< ?M3 (bag ?d2)) (< (bag ?d2) ?M4)
		(< (bagunion ?M3 (bag ?d2) ?M4) (bag ?d1)) (< (bag ?d1) ?M5) 
		(= ?N1 (+ ?N5 1))
		(= ?N3 ?N4) (= ?N3 ?N5) 
		(= ?C1 1) (= ?C3 1) (= ?C4 1) (= ?C5 0) (= ?c1 1) (= ?c2 0)
	)
	)

	(exists ( (?X Rbt_t) (?Y Rbt_t) (?U Rbt_t) (?V Rbt_t) (?M3 BagInt) (?N3 Int) (?C3 Int) (?M4 BagInt) (?N4 Int)  (?C4 Int)
		(?M5 BagInt) (?N5 Int) (?C5 Int) (?d1 Int) (?c1 Int) (?d2 Int) (?c2 Int) ) 
	(and (distinct ?E ?F) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d1) (ref color ?c1)) ) 
			(pto ?X (sref (ref left ?U) (ref right ?V) (ref data ?d2) (ref color ?c2)) )
			(rbt ?U ?M3 ?N3 ?C3) 
			(brrbthole ?V ?F ?M4 ?N4 ?C4 ?M2 ?N2 ?C2)
			(rbt ?Y ?M5 ?N5 ?C5)
		)
		)
		(= ?M1 (bagunion ?M3 (bag ?d2) ?M4 (bag ?d1) ?M5) )
		(< ?M3 (bag ?d2)) (< (bag ?d2) ?M4)
		(< (bagunion ?M3 (bag ?d2) ?M4) (bag ?d1)) (< (bag ?d1) ?M5) 
		(= ?N1 (+ ?N5 1))
		(= ?N3 ?N4) (= ?N3 ?N5)
		(= ?C1 1)  (= ?C3 1) (= ?C4 1) (= ?C5 0) (= ?c1 1) (= ?c2 0)
	)
	)

	(exists ( (?X Rbt_t) (?Y Rbt_t) (?U Rbt_t) (?V Rbt_t) (?M3 BagInt) (?N3 Int) (?C3 Int) (?M4 BagInt) (?N4 Int)  (?C4 Int)
		(?M5 BagInt) (?N5 Int) (?C5 Int) (?d1 Int) (?c1 Int) (?d2 Int) (?c2 Int) ) 
	(and (distinct ?E ?F) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d1) (ref color ?c1)) ) 
			(rbt ?X ?M3 ?N3 ?C3)
			(pto ?Y (sref (ref left ?U) (ref right ?V) (ref data ?d2) (ref color ?c2)) )
			(brrbthole ?U ?F ?M4 ?N4 ?C4 ?M2 ?N2 ?C2)
			(rbt ?V ?M5 ?N5 ?C5) 
		)
		)
		(= ?M1 (bagunion ?M3 (bag ?d1) ?M4 (bag ?d2) ?M5 ) )
		(< ?M4 (bag ?d2)) (< (bag ?d2) ?M5)
		(< ?M3 (bag ?d1)) (< (bag ?d1) (bagunion ?M4 (bag ?d2) ?M5))  
		(= ?N1 (+ ?N3 1))
		(= ?N4 ?N5) (= ?N3 ?N5)
		(= ?C1 1)  (= ?C3 0) (= ?C4 1) (= ?C5 1) (= ?c1 1) (= ?c2 0)
	)
	)

	(exists ( (?X Rbt_t) (?Y Rbt_t) (?U Rbt_t) (?V Rbt_t) (?M3 BagInt) (?N3 Int) (?C3 Int) (?M4 BagInt) (?N4 Int)  (?C4 Int)
		(?M5 BagInt) (?N5 Int) (?C5 Int) (?d1 Int) (?c1 Int) (?d2 Int) (?c2 Int) ) 
	(and (distinct ?E ?F) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d1) (ref color ?c1)) ) 
			(rbt ?X ?M3 ?N3 ?C3)
			(pto ?Y (sref (ref left ?U) (ref right ?V) (ref data ?d2) (ref color ?c2)) )
			(rbt ?U ?M4 ?N4 ?C4) 
			(brrbthole ?V ?F ?M5 ?N5 ?C5 ?M2 ?N2 ?C2)
		)
		)
		(= ?M1 (bagunion ?M3 (bag ?d1) ?M4 (bag ?d2) ?M5 ) )
		(< ?M4 (bag ?d2)) (< (bag ?d2) ?M5)
		(< ?M3 (bag ?d1)) (< (bag ?d1) (bagunion ?M4 (bag ?d2) ?M5))  
		(= ?N1 (+ ?N3 1))
		(= ?N4 ?N5) (= ?N3 ?N4)
		(= ?C1 1)  (= ?C3 0) (= ?C4 1) (= ?C5 1) (= ?c1 1) (= ?c2 0)
	)
	)
	)
))


;; the dual predicate of brrbthole, with red and black exchanged

;; rbrbthole(E,F, M1, N1, C1, M2, N2, C2)::= E = F & emp & M1 = M2 & H1 = H2 & C1 = C2 | 
;; exists X,Y,U,V,M3,M4,M5,H3,H4,H5,C3,C4,C5. E |-> ((left,X), (right,Y)) * Y |->((left,U),(right,V)) * rbt(X,M3,N3,C3) * 
;; rbrbthole(U,F,M4,N4,C4,M2,N2,C2) * rbt(V,M5,N5,C5) & M1 = {E.data} cup M3 cup {Y.data} cup M4 cup M5 & M3 < E.data < 
;; {Y.data} cup M4 cup M5 & M4 < Y.data < M5 & C1 = E.color & C1 = 0 & C3 = 1 & Y.color = 1 & C4 = 0 & N4 = N5 & N3 = N4 + 1 & 
;; N1 = N3 |
;; exists X,Y,U,V,M3,M4,M5,H3,H4,H5,C3,C4,C5. E |-> ((left,X), (right,Y)) * Y |->((left,U),(right,V)) * rbt(X,M3,N3,C3) * 
;; rbt(U,M4,N4,C4) * rbrbthole(V,F,M5,N5,C5,M2,N2,C2) & M1 = {E.data} cup M3 cup {Y.data} cup M4 cup M5 & M3 < E.data < 
;; {Y.data} cup M4 cup M5 & M4 < Y.data < M5 & C1 = E.color & C1 = 0 & C3 = 1 & Y.color = 1 & C5 = 0 & N4 = N5 & N3 = N4 + 1 & 
;; N1 = N3 |
;; exists X,Y,U,V,M3,M4,M5,H3,H4,H5,C3,C4,C5. E |-> ((left,X), (right,Y)) * X |->((left,U),(right,V)) * rbt(U,M3,N3,C3) * 
;; rbrbthole(V,F,M4,N4,C4,M2,N2,C2) * rbt(Y,M5,N5,C5) & M1 = {E.data} cup {X.data} cup M3 cup M4 cup M5 & {X.data} cup M3 cup M4 <
;; E.data < M5 & M3 < X.data < M4 & C1 = E.color & C1 = 0 & X.color = 1 & C5 = 1 & C4 = 0 & N3 = N4 & N5 = N3+1 & N1 = N5 |
;; exists X,Y,U,V,M3,M4,M5,H3,H4,H5,C3,C4,C5. E |-> ((left,X), (right,Y)) * X |->((left,U),(right,V)) * 
;; rbrbthole(U,F,M3,N3,C3, M2, N2, C2) * rbt(V,M4,N4,C4) * rbt(Y,M5,N5,C5) & M1 = {E.data} cup {X.data} cup M3 cup M4 cup M5 &
;; {X.data} cup M3 cup M4 < E.data < M5 & M3 < X.data < M4 & C1 = E.color & C1 = 0 & X.color = 1 & C5 = 1 & C3 = 0 & N3 = N4 & 
;; N5 = N3+1 & N1 = N5


(define-fun rbrbthole ((?E Rbt_t) (?F Rbt_t) (?M1 BagInt) (?N1 Int) (?C1 Int) (?M2 BagInt) (?N2 Int) (?C2 Int)) Space (tospace 
	(or 
	(and (= ?E ?F) 
		(tobool emp
		)
		(= ?M1 ?M2)
		(= ?N1 ?N2)
		(= ?C1 ?C2)
	)
 
	(exists ( (?X Rbt_t) (?Y Rbt_t) (?U Rbt_t) (?V Rbt_t) (?M3 BagInt) (?N3 Int) (?C3 Int) (?M4 BagInt) (?N4 Int) (?C4 Int)
		(?M5 BagInt) (?N5 Int) (?C5 Int) (?d1 Int) (?d2 Int) (?c1 Int) (?c2 Int) ) 
	(and (distinct ?E ?F) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d1) (ref color ?c1)) ) 
			(pto ?X (sref (ref left ?U) (ref right ?V) (ref data ?d2) (ref color ?c2)) )
			(rbrbthole ?U ?F ?M3 ?N3 ?C3 ?M2 ?N2 ?C2)
			(rbt ?V ?M4 ?N4 ?C4) 
			(rbt ?Y ?M5 ?N5 ?C5)
		)
		)
		(= ?M1 (bagunion ?M3 (bag ?d2) ?M4 (bag ?d1) ?M5) )
		(< ?M3 (bag ?d2)) (< (bag ?d2) ?M4)
		(< (bagunion ?M3 (bag ?d2) ?M4) (bag ?d1)) (< (bag ?d1) ?M5) 
		(= ?N1 (+ ?N5 1))
		(= ?N3 ?N4) (= ?N3 ?N5) 
		(= ?C1 0) (= ?C3 0) (= ?C4 0) (= ?C5 1) (= ?c1 0) (= ?c2 1)
	)
	)

	(exists ( (?X Rbt_t) (?Y Rbt_t) (?U Rbt_t) (?V Rbt_t) (?M3 BagInt) (?N3 Int) (?C3 Int) (?M4 BagInt) (?N4 Int)  (?C4 Int)
		(?M5 BagInt) (?N5 Int) (?C5 Int) (?d1 Int) (?c1 Int) (?d2 Int) (?c2 Int) ) 
	(and (distinct ?E ?F) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d1) (ref color ?c1)) ) 
			(pto ?X (sref (ref left ?U) (ref right ?V) (ref data ?d2) (ref color ?c2)) )
			(rbt ?U ?M3 ?N3 ?C3) 
			(rbrbthole ?V ?F ?M4 ?N4 ?C4 ?M2 ?N2 ?C2)
			(rbt ?Y ?M5 ?N5 ?C5)
		)
		)
		(= ?M1 (bagunion ?M3 (bag ?d2) ?M4 (bag ?d1) ?M5) )
		(< ?M3 (bag ?d2)) (< (bag ?d2) ?M4)
		(< (bagunion ?M3 (bag ?d2) ?M4) (bag ?d1)) (< (bag ?d1) ?M5) 
		(= ?N1 (+ ?N5 1))
		(= ?N3 ?N4) (= ?N3 ?N5)
		(= ?C1 0)  (= ?C3 0) (= ?C4 0) (= ?C5 1) (= ?c1 0) (= ?c2 1)
	)
	)

	(exists ( (?X Rbt_t) (?Y Rbt_t) (?U Rbt_t) (?V Rbt_t) (?M3 BagInt) (?N3 Int) (?C3 Int) (?M4 BagInt) (?N4 Int)  (?C4 Int)
		(?M5 BagInt) (?N5 Int) (?C5 Int) (?d1 Int) (?c1 Int) (?d2 Int) (?c2 Int) ) 
	(and (distinct ?E ?F) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d1) (ref color ?c1)) ) 
			(rbt ?X ?M3 ?N3 ?C3)
			(pto ?Y (sref (ref left ?U) (ref right ?V) (ref data ?d2) (ref color ?c2)) )
			(rbrbthole ?U ?F ?M4 ?N4 ?C4 ?M2 ?N2 ?C2)
			(rbt ?V ?M5 ?N5 ?C5) 
		)
		)
		(= ?M1 (bagunion ?M3 (bag ?d1) ?M4 (bag ?d2) ?M5 ) )
		(< ?M4 (bag ?d2)) (< (bag ?d2) ?M5)
		(< ?M3 (bag ?d1)) (< (bag ?d1) (bagunion ?M4 (bag ?d2) ?M5))  
		(= ?N1 (+ ?N3 1))
		(= ?N4 ?N5) (= ?N3 ?N5)
		(= ?C1 0)  (= ?C3 1) (= ?C4 0) (= ?C5 0) (= ?c1 0) (= ?c2 1)
	)
	)

	(exists ( (?X Rbt_t) (?Y Rbt_t) (?U Rbt_t) (?V Rbt_t) (?M3 BagInt) (?N3 Int) (?C3 Int) (?M4 BagInt) (?N4 Int)  (?C4 Int)
		(?M5 BagInt) (?N5 Int) (?C5 Int) (?d1 Int) (?c1 Int) (?d2 Int) (?c2 Int) ) 
	(and (distinct ?E ?F) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d1) (ref color ?c1)) ) 
			(rbt ?X ?M3 ?N3 ?C3)
			(pto ?Y (sref (ref left ?U) (ref right ?V) (ref data ?d2) (ref color ?c2)) )
			(rbt ?U ?M4 ?N4 ?C4) 
			(rbrbthole ?V ?F ?M5 ?N5 ?C5 ?M2 ?N2 ?C2)
		)
		)
		(= ?M1 (bagunion ?M3 (bag ?d1) ?M4 (bag ?d2) ?M5 ) )
		(< ?M4 (bag ?d2)) (< (bag ?d2) ?M5)
		(< ?M3 (bag ?d1)) (< (bag ?d1) (bagunion ?M4 (bag ?d2) ?M5))  
		(= ?N1 (+ ?N3 1))
		(= ?N4 ?N5) (= ?N3 ?N4)
		(= ?C1 0)  (= ?C3 1) (= ?C4 0) (= ?C5 0) (= ?c1 0) (= ?c2 1)
	)
	)
	)
))

;; declare variables
(declare-fun root () Rbt_t)
(declare-fun root0 () Rbt_t)
(declare-fun cur () Rbt_t)
(declare-fun cur1 () Rbt_t)
(declare-fun cur2 () Rbt_t)
(declare-fun parent () Rbt_t)
(declare-fun parent0 () Rbt_t)
(declare-fun parent1 () Rbt_t)
(declare-fun parent2 () Rbt_t)
(declare-fun uncle () Rbt_t)
(declare-fun uncle1 () Rbt_t)
(declare-fun uncle2 () Rbt_t)
(declare-fun grandpa () Rbt_t)
(declare-fun grandpa1 () Rbt_t)
(declare-fun grandpa2 () Rbt_t)
(declare-fun ggrandpa () Rbt_t)
(declare-fun ggrandpa1 () Rbt_t)
(declare-fun ggrandpa2 () Rbt_t)
(declare-fun cusparent () Rbt_t)
(declare-fun cusparent1 () Rbt_t)
(declare-fun cusparent2 () Rbt_t)
(declare-fun cusnode () Rbt_t)
(declare-fun cusnode1 () Rbt_t)
(declare-fun cusnode2 () Rbt_t)
(declare-fun cu () Rbt_t)
(declare-fun cu1 () Rbt_t)
(declare-fun cu2 () Rbt_t)
(declare-fun pa () Rbt_t)
(declare-fun ggra () Rbt_t)
(declare-fun gra () Rbt_t)
(declare-fun unc () Rbt_t)
(declare-fun ret () Rbt_t)

(declare-fun x () Rbt_t)
(declare-fun X () Rbt_t)
(declare-fun Y () Rbt_t)
(declare-fun Z () Rbt_t)
(declare-fun U () Rbt_t)
(declare-fun V () Rbt_t)
(declare-fun W () Rbt_t)
(declare-fun U1 () Rbt_t)
(declare-fun V1 () Rbt_t)
(declare-fun U2 () Rbt_t)
(declare-fun V2 () Rbt_t)

(declare-fun M0 () BagInt)
(declare-fun M1 () BagInt)
(declare-fun M2 () BagInt)
(declare-fun M3 () BagInt)
(declare-fun M4 () BagInt)
(declare-fun M5 () BagInt)
(declare-fun M6 () BagInt)
(declare-fun M7 () BagInt)
(declare-fun M8 () BagInt)
(declare-fun M9 () BagInt)
(declare-fun M10 () BagInt)
(declare-fun M11 () BagInt)
(declare-fun M12 () BagInt)
(declare-fun M13 () BagInt)
(declare-fun M14 () BagInt)
(declare-fun M15 () BagInt)
(declare-fun M16 () BagInt)
(declare-fun M17 () BagInt)
(declare-fun M18 () BagInt)
(declare-fun M19 () BagInt)
(declare-fun M20 () BagInt)

(declare-fun N1 () Int)
(declare-fun N2 () Int)
(declare-fun N3 () Int)
(declare-fun N4 () Int)
(declare-fun N5 () Int)
(declare-fun N6 () Int)
(declare-fun N7 () Int)
(declare-fun N8 () Int)
(declare-fun N9 () Int)
(declare-fun N10 () Int)
(declare-fun N11 () Int)
(declare-fun N12 () Int)
(declare-fun N13 () Int)
(declare-fun N14 () Int)
(declare-fun N15 () Int)
(declare-fun N16 () Int)
(declare-fun N17 () Int)
(declare-fun N18 () Int)
(declare-fun N19 () Int)
(declare-fun N20 () Int)

(declare-fun n1 () Int)
(declare-fun n2 () Int)
(declare-fun n3 () Int)
(declare-fun n4 () Int)
(declare-fun n5 () Int)
(declare-fun n6 () Int)
(declare-fun n7 () Int)
(declare-fun n8 () Int)
(declare-fun n9 () Int)
(declare-fun n10 () Int)
(declare-fun iseven () Int)

(declare-fun C1 () Int)
(declare-fun C2 () Int)
(declare-fun C3 () Int)
(declare-fun C4 () Int)
(declare-fun C5 () Int)
(declare-fun C6 () Int)
(declare-fun C7 () Int)
(declare-fun C8 () Int)
(declare-fun C9 () Int)
(declare-fun C10 () Int)
(declare-fun C11 () Int)
(declare-fun C12 () Int)
(declare-fun C13 () Int)
(declare-fun C14 () Int)
(declare-fun C15 () Int)
(declare-fun C16 () Int)
(declare-fun C17 () Int)
(declare-fun C18 () Int)
(declare-fun C19 () Int)
(declare-fun C20 () Int)

(declare-fun d1 () Int)
(declare-fun d2 () Int)
(declare-fun d3 () Int)
(declare-fun d4 () Int)
(declare-fun d5 () Int)
(declare-fun d6 () Int)
(declare-fun d7 () Int)
(declare-fun d8 () Int)
(declare-fun d9 () Int)
(declare-fun d10 () Int)
(declare-fun cz () Int)
(declare-fun c1 () Int)
(declare-fun c2 () Int)
(declare-fun c3 () Int)
(declare-fun c4 () Int)
(declare-fun c5 () Int)
(declare-fun c6 () Int)
(declare-fun c7 () Int)
(declare-fun c8 () Int)
(declare-fun c9 () Int)
(declare-fun c10 () Int)

(declare-fun key () Int)

;; declare set of locations

(declare-fun alpha0 () SetLoc)
(declare-fun alpha00 () SetLoc)
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
(declare-fun alpha20 () SetLoc)
(declare-fun alpha21 () SetLoc)
(declare-fun alpha22 () SetLoc)
(declare-fun alpha23 () SetLoc)
(declare-fun alpha24 () SetLoc)



;; VC19:
;; cusnode |-> ((left,V1),(right,unc),(data,d1),(color,0)) * rbt(unc,M2,N2,C2) * pa |-> ((left,X),(right,U1),(data,d2),(color,c2)) * rbt(X,M3,N3,C3) 
;; * gra |-> ((left,pa),(right,cusnode),(data,d3),(color,1)) * rbt(V1,M8,N8,1) * U1|-> ((left,U2),(right,V2),(data,d4),(color,1)) * rbt(V2,M9,N9,C9) 
;; * rbrbthole(U2,x,M10,N10,0,M5,N5,0) * x |-> ((left,nil),(right,nil),(data,key),(color,0)) & 
;; M10 < d4 < M9 & N10 = N9 & M10 cup {d4} cup M9 < d3 < M8 & N9+1 = N8 & M4 = M10 cup {d4} cup M9 cup {d3} cup M8 & N4 = N8 & M5 = {key} & N5 = 1 & 
;; M3 < d2 < M4 & N3 = N4 & 0 <= c2 <= 1 & (c2 =0 => C3 =1) & {d2} cup M4 cup M3 < d1 < M2 & n2 = ite(c2 =0, N3, N3+1) & n2=N2 & 0 <=c1 <= 1 & (c1=0 
;; => c2 = 1 & C2=1) & M0 cup {key} = {d2} cup M4 cup M3 cup {d1} cup M2 & ! key in M0 & cusparent = nil & c2 = 0  & C2 = 1 & root = gra & ret = root 
;; & M7 = {d2} cup M4 cup M3 cup {d1} cup M2 & N7 = N3+1 & C7=1
;; |-
;; rbt(ret,M7,N7,C7) & M7 = M0 cup {key} & ! key in M0


(assert 
	(and
	(tobool 
	(ssep 
		(pto cusnode (sref (ref left V1) (ref right unc) (ref data d1) (ref color c1)))
		(index alpha1 (rbt unc M2 N2 C2)) 
		(pto pa (sref (ref left X) (ref right U1) (ref data d2) (ref color c2)))
		(index alpha2 (rbt X M3 N3 C3))
		(pto gra (sref (ref left pa) (ref right cusnode) (ref data d3) (ref color c3)))
		(index alpha3 (rbt V1 M8 N8 C8))
		(pto U1 (sref (ref left U2) (ref right V2) (ref data d4) (ref color c4)))
		(index alpha4 (rbt V2 M9 N9 C9))
		(index alpha5 (rbrbthole U2 x M10 N10 C10 M5 N5 C5))
		(pto x (sref (ref left nil) (ref right nil) (ref data key) (ref color c5))) 
	))
	(< M10 (bag d4)) (< (bag d4) M9) (= N10 N9) (< (bagunion M10 (bag d4) M9) (bag d3)) (< (bag d3) M8)
	(= (+ N9 1) N8) (= M4 (bagunion M10 (bag d4) M9 (bag d3) M8) ) (= N4 N8)
	(= M5 (bag key) ) (= N5  1) (< M3 (bag d2)) (< (bag d2) M4) (= N3 N4) (<= 0 c2) (<= c2 1)
	(=> (= c2 0) (= C3 1) ) (< (bagunion (bag d2) M4 M3) (bag d1)) (< (bag d1) M2)
	(= N2 (ite (= c2 0) N3 (+ N3 1)) )(<= 0 c1) (<= c1 1) (=> (= c1 0) (= c2 1)) (=> (= c1 0) (= C2 1) ) 
	(= (bagunion M0 (bag key) ) (bagunion (bag d2) M4 M3 (bag d1) M2) ) (= M0 (bagminus M0 (bag key)) )
	(= cusparent nil) (= c2 0) (= C2 1) (= root gra) (= ret root) (= M7 (bagunion (bag d2) M4 M3 (bag d1) M2) ) 
	(= N7 (+ N3 1) ) (= c1 0) (= C7 1) (= c3 1) (= C8 1) (= c4 1) (= C10 0) (= C5 0) (= c5 0)
	)
)

;; rbt(ret,M7,N7,C7) & M7 = M0 cup {key} & ! key in M0

(assert (not 
	(and 
	(tobool 
		(index alpha7 (rbt ret M7 N7 C7))
	)
	(= M7 (bagunion M0 (bag key)) ) (= M0 (bagminus M0 (bag key)) )
	)
))

(check-sat)
