;(set-logic AUFLIRA)

;(declare-sort Point)
;(declare-sort Line)
;(declare-sort Circle)

;(declare-fun Between (Point Point Point) Bool)
;(declare-fun On_L (Point Line) Bool)
;(declare-fun On_C (Point Circle) Bool)
;(declare-fun Inside (Point Circle) Bool)
;(declare-fun Center (Point Circle) Bool)
;(declare-fun SameSide (Point Point Line) Bool)
;(declare-fun Intersects_LL (Line Line) Bool)
;(declare-fun Intersects_LC (Line Circle) Bool)
;(declare-fun Intersects_CC (Circle Circle) Bool)

;(declare-fun Segment_PP (Point Point) Real)
;(declare-fun Angle_PPP (Point Point Point) Real)
;(declare-fun Area_PPP (Point Point Point) Real)
;(declare-const RightAngle Real)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Diagrammatic axioms
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;
; Generalities
;

; Two points determine a line
(assert 
    (forall ((a Point) (b Point) (L Line) (M Line))   
        (=> 
            (and 
                (not (= a b)) 
                (On_L a L) 
                (On_L b L) 
                (On_L a M) 
                (On_L b M)
            )
            (= L M)
        )
    )
)

; Center is unique
(assert
    (forall ((a Point) (b Point) (C Circle))
        (=> 
            (and (Center a C) (Center b C))
            (= a b)
        )
    )
)

(assert
    (forall ((a Point) (C Circle))
        (=>
            (Center a C)
            (Inside a C)
        )
    )
)


;
; Between axioms
;

(assert
    (forall ((a Point) (b Point) (c Point))
        (=>
            (Between a b c)
            (and
                (Between c b a)
                (not (= a b))
                (not (= a c))
                (not (Between b a c))
            )
        )
    )
)

(assert
    (forall ((a Point) (b Point) (c Point) (L Line))
        (=>
            (and (Between a b c) (On_L a L) (On_L b L))
            (On_L c L)
        )
    )
)

(assert
    (forall ((a Point) (b Point) (c Point) (L Line))
        (=>
            (and (Between a b c) (On_L a L) (On_L c L)) 
            (On_L b L)
        )
    )
)

(assert
    (forall ((a Point) (b Point) (c Point) (d Point))
        (=> 
            (and 
                (Between a b c) 
                (Between a d b)
            )
            (Between a d c)
        )
    )
)

(assert
    (forall ((a Point) (b Point) (c Point) (d Point))
        (=> 
            (and 
                (Between a b c) 
                (Between b c d)
            )
            (Between a b d)
        )
    )
)

(assert 
    (forall ((a Point) (b Point) (c Point) (L Line))
       (=> 
            (and 
                (On_L a L) 
                (On_L b L) 
                (On_L c L)
                (not (= a b)) 
                (not (= a c))
                (not (= b c))
            )
            (or 
                (Between a b c) 
                (Between b a c) 
                (Between a c b)
            )
        )
    )
)

;
; Same side axioms
;

(assert
    (forall ((a Point) (L Line))
        (=> 
            (not (On_L a L)) 
            (SameSide a a L)
        )
    )
)

(assert 
    (forall ((a Point) (b Point) (L Line))
        (=> 
            (SameSide a b L)
            (and 
                (not (On_L a L))
                (SameSide b a L)
            )
        )
    )
)

(assert 
    (forall ((a Point) (b Point) (c Point) (L Line))
        (=> 
            (and 
                (SameSide a b L) 
                (SameSide a c L)
            )
            (SameSide b c L)
        )
    )
)

(assert 
    (forall ((a Point) (b Point) (c Point) (L Line))
        (=> 
            (and 
                (not (On_L a L))
                (not (On_L b L))
                (not (On_L c L))
            )
            (or 
                (SameSide a b L) 
                (SameSide a c L) 
                (SameSide b c L)
            )
        )
    )
)


;
; Pasch axioms
;

(assert 
    (forall ((a Point) (b Point) (c Point) (L Line))
        (=> 
            (and 
                (Between a b c) 
                (SameSide a c L)
            )
            (SameSide a b L)
        )
    )
)

(assert 
    (forall ((a Point) (b Point) (c Point) (L Line))
        (=> 
            (and 
                (Between a b c) 
                (On_L a L) 
                (not (On_L b L))
            )
            (SameSide b c L)
        )
    )
)

(assert
    (forall ((a Point) (b Point) (c Point) (L Line))
        (=> 
            (and 
                (Between a b c) 
                (On_L b L)
            )
            (not (SameSide a c L))
        )
    )
)

(assert
    (forall ((a Point) (b Point) (c Point) (L Line) (M Line))
        (=> 
            (and 
                (not (= a b)) 
                (not (= b c)) 
                (not (= L M)) 
                (On_L a M)
                (On_L b M) 
                (On_L c M)
                (not (SameSide a c L)) 
                (On_L b L)
            )
            (Between a b c)
        )
    )
)


;
; Triple incidence axioms
;

(assert
    (forall ((a Point) (b Point) (c Point) (d Point) (L Line) (M Line) (N Line))
        (=> 
            (and 
                (On_L a L) 
                (On_L a M) 
                (On_L a N) 
                (On_L b L) 
                (On_L c M) 
                (On_L d N) 
                (SameSide c d L) 
                (SameSide b c N)
            )
            (not (SameSide b d M))
        )
    )
)

(assert
    (forall ((a Point) (b Point) (c Point) (d Point) (L Line) (M Line) (N Line))
        (=> 
            (and 
                (On_L a L) 
                (On_L a M) 
                (On_L a N) 
                (On_L b L) 
                (On_L c M) 
                (On_L d N)
                (SameSide c d L)
                (not (SameSide d b M)) 
                (not (On_L d M))
                (not (= b a))
            )
            (SameSide b c N)
        )
    )
)


(assert
    (forall ((a Point) (b Point) (c Point) (d Point) (e Point) (L Line) (M Line) (N Line))
        (=> 
            (and 
                (On_L a L) 
                (On_L a M) 
                (On_L a N) 
                (On_L b L) 
                (On_L c M) 
                (On_L d N) 
                (SameSide b c N) 
                (SameSide d c L)
                (SameSide d e M) 
                (SameSide c e N)
            )
            (SameSide c e L)
        )
    )
)


;
; Circle axioms
;

(assert
    (forall ((a Point) (b Point) (c Point) (C Circle) (L Line))
        (=> 
            (and 
                (Inside a C) 
                (On_C b C) 
                (On_C c C) 
                (On_L a L)
                (On_L b L) 
                (On_L c L) 
                (not (= b c))
            )
            (Between b a c)
        )
    )
)

(assert
    (forall ((a Point) (b Point) (c Point) (C Circle))
        (=> 
            (and 
                (or 
                    (Inside a C) 
                    (On_C a C)
                )
                (or 
                    (Inside b C) 
                    (On_C b C)
                )
                (Between a c b)
            )
            (Inside c C)
        )
    )
)

(assert
    (forall ((a Point) (b Point) (c Point) (C Circle))
        (=> 
            (and 
                (or 
                    (Inside a C) 
                    (On_C a C)
                ) 
                (not (Inside c C)) 
                (Between a c b)
            )
            (and 
                (not (Inside b C)) 
                (not (On_C b C))
            )
        )
    )
)

(assert
    (forall ((a Point) (b Point) (c Point) (d Point) (C Circle) (D Circle) (L Line))
        (=> 
            (and 
                (On_C c C) 
                (On_C c D) 
                (On_C d C) 
                (On_C d D) 
                (not (= C D)) 
                (not (= c d))
                (On_L a L) 
                (On_L b L) 
                (Center a C) 
                (Center a D)
            )
            (not (SameSide c d L))
        )
    )
)

;
; IntersectiOn_Ls
;

(assert
    (forall ((L Line) (M Line) (a Point) (b Point))
        (=> 
            (and 
                (On_L a M) 
                (On_L b M) 
                (not (On_L a L))
                (not (On_L b L))
                (not (SameSide a b L))
            )
            (Intersects_LL L M)
        )
    )
)

(assert
    (forall ((C Circle) (L Line) (a Point) (b Point))
        (=> 
            (and 
                (or 
                    (Inside a C) 
                    (On_C a C)
                ) 
                (or 
                    (Inside b C) 
                    (On_C b C)
                )
                (not (On_L a L)) 
                (not (On_L b L)) 
                (not (SameSide a b L))
            )
            (Intersects_LC L C)
        )
    )
)

(assert
    (forall ((L Line) (C Circle) (a Point))
        (=> 
            (and 
                (Inside a C)
                (On_L a L)
            )
            (Intersects_LC L C)
        )
    )
) 

(assert
    (forall ((C Circle) (D Circle) (a Point) (b Point))
        (=> 
            (and 
                (or
                    (Inside a C)
                    (On_C a C)
                )
                (or 
                    (Inside b C)
                    (On_C b C)
                )
                (Inside a D)
                (not (Inside b D))
                (not (On_C b D))
            )
            (Intersects_CC C D)
        )
    )
)

(assert
    (forall ((C Circle) (D Circle) (a Point) (b Point))
        (=> 
            (and 
                (On_C a C) 
                (Inside b C) 
                (Inside a D) 
                (On_C b D)
            )
            (Intersects_CC C D)
        )
    )
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Metric axioms
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Segment_PPPments

(assert
    (forall ((a Point) (b Point)) 
        (=> 
            (= (Segment_PP a b) 0.0) 
            (= a b)
        )
    )
)

(assert
    (forall ((a Point)) 
        (= (Segment_PP a a) 0.0)
    )
)

(assert
    (forall ((a Point) (b Point)) 
        (>= (Segment_PP a b) 0.0)
    )
)

(assert
    (forall ((a Point) (b Point)) 
        (= (Segment_PP a b) (Segment_PP b a))
    )
)

; Angle_PPPs

(assert
    (forall ((a Point) (b Point) (c Point))
        (=> 
            (and 
                (not (= a b)) 
                (not (= b c))
            )
            (= (Angle_PPP a b c) (Angle_PPP c b a))
        )
    )
)

(assert
    (forall ((a Point) (b Point) (c Point))
        (=> 
            (and 
                (not (= a b)) 
                (not (= b c))
            )
            (and 
                (>= (Angle_PPP a b c) 0.0) 
                (<= (Angle_PPP a b c) 
                (+ RightAngle RightAngle))
            )
        ) 
    )
)

; Area_PPPs

(assert
    (forall ((a Point) (b Point))
        (= (Area_PPP a a b) 0.0)
    )
)

(assert
    (forall ((a Point) (b Point) (c Point))
        (>= (Area_PPP a b c) 0.0)
    )
)

(assert
    (forall ((a Point) (b Point) (c Point))
        (and 
            (= (Area_PPP a b c) (Area_PPP c a b)) 
            (= (Area_PPP a b c) (Area_PPP a c b))
        )
    )
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Transfer axioms
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;
; Diagram-Segment_PPPment transfer axioms
;

(assert
    (forall ((a Point) (b Point) (c Point))
        (=> 
            (Between a b c) 
            (= (+ (Segment_PP a b) (Segment_PP b c)) (Segment_PP a c))
        )
    )
)


; center and radius determines the circle

(assert
    (forall ((a Point) (b Point) (c Point) (C Circle) (D Circle))
        (=> 
            (and 
                (Center a C) 
                (Center a D) 
                (On_C b C) 
                (On_C c D)
                (= (Segment_PP a b) (Segment_PP a c))
            )
            (= C D)
        )
    )
)


(assert
    (forall ((a Point) (b Point) (c Point) (C Circle))
        (=> 
            (and 
                (Center a C) 
                (On_C b C) 
                (= (Segment_PP a c) (Segment_PP a b))
            )
            (On_C c C)
        )
    )
)


(assert
    (forall ((a Point) (b Point) (c Point) (C Circle))
        (=> 
            (and 
                (Center a C) 
                (On_C b C)
            )
            (= 
                (< (Segment_PP a c) (Segment_PP a b)) 
                (Inside c C)
            )
        )
    )
)


;
; Diagram-Angle_PPP transfer axioms
;

; colinear iff Angle_PPP is equal to 0
(assert
    (forall ((a Point) (b Point) (c Point) (L Line))
        (=> 
            (and 
                (not (= a b)) 
                (not (= a c)) 
                (On_L a L) 
                (On_L b L)
            )
            (= 
                (and 
                    (On_L c L) 
                    (not (Between c a b))
                )
                (= (Angle_PPP b a c) 0.0)
            )
        )
    )
)


(assert
    (forall ((a Point) (b Point) (c Point) (d Point) (L Line) (M Line))
        (=> 
            (and 
                (On_L a L) 
                (On_L b L) 
                (On_L a M) 
                (On_L c M)
                (not (= a b)) 
                (not (= a c)) 
                (not (On_L d L)) 
                (not (On_L d M)) 
                (not (= L M))
            )
            (= 
                (= (Angle_PPP b a c) (+ (Angle_PPP b a d) (Angle_PPP d a c)))
                (and 
                    (SameSide b d M) 
                    (SameSide d c L)
                )
            )
        )
    )
)


; def right Angle_PPP (and all right Angle_PPPs are equal)
(assert
    (forall ((a Point) (b Point) (c Point) (d Point) (L Line))
        (=> 
            (and 
                (On_L a L) 
                (On_L b L) 
                (Between a c b) 
                (not (On_L d L))
            )
            (= 
                (= (Angle_PPP a c d) (Angle_PPP d c b))
                (= (Angle_PPP a c d) RightAngle)
            )
        )
    )
)

(assert
    (forall ((a Point) (b Point) (c Point) (L Line))
        (=> 
            (and 
                (On_L a L) 
                (On_L b L) 
                (not (= a b)))
            (= 
                (= (Area_PPP a b c) 0.0)
                (On_L c L)
            )
        )
    )
)


; Area_PPPs sum
(assert
    (forall ((a Point) (b Point) (c Point) (d Point) (L Line))
        (=> 
            (and 
                (On_L a L) 
                (On_L b L) 
                (On_L c L) 
                (not (On_L d L)) 
                (not (= a b)) 
                (not (= c a)) 
                (not (= c b))
            )
            (= 
                (Between a c b)
                (= 
                    (+ (Area_PPP a c d) (Area_PPP d c b)) 
                    (Area_PPP a d b)
                )
            )
        )
    )
)


;(check-sat)
;(get-model)