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

; two_points_determine_line
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

; center_unique
(assert
    (forall ((a Point) (b Point) (alpha Circle))
        (=> 
            (and 
                (Center a alpha) 
                (Center b alpha)
            )
            (= a b)
        )
    )
)

; center_inside_circle
(assert
    (forall ((a Point) (alpha Circle))
        (=>
            (Center a alpha)
            (Inside a alpha)
        )
    )
)

; inside_not_on_circle
(assert 
    (forall ((a Point) (alpha Circle))
        (=>
            (Inside a alpha)
            (not (On_C a alpha))
        )
    )
)

; between_symm
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

; between_same_line_c
(assert
    (forall ((a Point) (b Point) (c Point) (L Line))
        (=>
            (and 
                (Between a b c) 
                (On_L a L) 
                (On_L b L)
            )
            (On_L c L)
        )
    )
)

; between_same_line_b
(assert
    (forall ((a Point) (b Point) (c Point) (L Line))
        (=>
            (and 
                (Between a b c) 
                (On_L a L) 
                (On_L c L)
            ) 
            (On_L b L)
        )
    )
)

; between_trans_in
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

; between_trans_out
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

; between_points
(assert 
    (forall ((a Point) (b Point) (c Point) (L Line))
       (=> 
            (and 
                (not (= a b)) 
                (not (= b c))
                (not (= c a))
                (On_L a L) 
                (On_L b L) 
                (On_L c L)
            )
            (or 
                (Between a b c) 
                (Between b a c) 
                (Between a c b)
            )
        )
    )
)

; between_not_trans
(assert 
    (forall ((a Point) (b Point) (c Point) (d Point))
        (=>
            (and
                (Between a b c)
                (Between a b d)
            )
            (not (Between c b d))
        )
    )
)

; same_side_refl
(assert
    (forall ((a Point) (L Line))
        (=> 
            (not (On_L a L)) 
            (SameSide a a L)
        )
    )
)

; same_side_symm
(assert 
    (forall ((a Point) (b Point) (L Line))
        (=> 
            (SameSide a b L)
            (SameSide b a L)
        )
    )
)

; same_side_not_on_line
(assert 
    (forall ((a Point) (b Point) (L Line))
        (=> 
            (SameSide a b L)
            (not (On_L a L))
        )
    )
)

; same_side_trans
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

; same_side_pigeon_hole
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

; pasch_1
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

; pasch_2
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

; pasch_3
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

; pasch_4
(assert
    (forall ((a Point) (b Point) (c Point) (L Line) (M Line))
        (=> 
            (and 
                (not (= L M)) 
                (On_L b L)
                (On_L b M) 
                (not (= a c))
                (On_L a M)
                (On_L c M)
                (not (= a b)) 
                (not (= c b)) 
                (not (SameSide a c L)) 
            )
            (Between a b c)
        )
    )
)

; triple_incidence_1
(assert
    (forall ((L Line) (M Line) (N Line) (a Point) (b Point) (c Point) (d Point))
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

; triple_incidence_2
(assert
    (forall ((L Line) (M Line) (N Line) (a Point) (b Point) (c Point) (d Point))
        (=> 
            (and 
                (On_L a L) 
                (On_L a M) 
                (On_L a N) 
                (On_L b L) 
                (On_L c M) 
                (On_L d N)
                (SameSide c d L)
                (not (SameSide b d M)) 
                (not (On_L d M))
                (not (= b a))
            )
            (SameSide b c N)
        )
    )
)

; triple_incidence_3
(assert
    (forall ((L Line) (M Line) (N Line) (a Point) (b Point) (c Point) (d Point) (e Point))
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
                (SameSide d e M) 
                (SameSide c e N)
            )
            (SameSide c e L)
        )
    )
)


; circle_line_intersections
(assert
    (forall ((a Point) (b Point) (c Point) (L Line) (alpha Circle))
        (=> 
            (and 
                (On_L a L)
                (On_L b L) 
                (On_L c L) 
                (Inside a alpha) 
                (On_C b alpha) 
                (On_C c alpha) 
                (not (= b c))
            )
            (Between b a c)
        )
    )
)

; circle_points_between
(assert
    (forall ((a Point) (b Point) (c Point) (alpha Circle))
        (=> 
            (and 
                (or 
                    (Inside a alpha) 
                    (On_C a alpha)
                )
                (or 
                    (Inside b alpha) 
                    (On_C b alpha)
                )
                (Between a c b)
            )
            (Inside c alpha)
        )
    )
)

; circle_points_extend
(assert
    (forall ((a Point) (b Point) (c Point) (alpha Circle))
        (=> 
            (and 
                (or 
                    (Inside a alpha) 
                    (On_C a alpha)
                ) 
                (not (Inside c alpha)) 
                (Between a c b)
            )
            (and 
                (not (Inside b alpha)) 
                (not (On_C b alpha))
            )
        )
    )
)

; circles_intersections_diff_side
(assert
    (forall ((a Point) (b Point) (c Point) (d Point) (alpha Circle) (beta Circle) (L Line))
        (=> 
            (and 
                (not (= alpha beta)) 
                (On_C c alpha) 
                (On_C c beta) 
                (On_C d alpha) 
                (On_C d beta)
                (not (= c d))
                (Center a alpha) 
                (Center b beta)
                (On_L a L) 
                (On_L b L)    
            )
            (not (SameSide c d L))
        )
    )
)

; intersection_lines
(assert
    (forall ((a Point) (b Point) (L Line) (M Line))
        (=> 
            (and 
                (not (On_L a L))
                (not (On_L b L))
                (not (SameSide a b L))
                (On_L a M) 
                (On_L b M) 
            )
            (Intersects_LL L M)
        )
    )
)

; intersection_circle_line_1
(assert
    (forall ((a Point) (b Point) (alpha Circle) (L Line))
        (=> 
            (and 
                (or 
                    (On_C a alpha)
                    (Inside a alpha)   
                ) 
                (or 
                    (On_C b alpha)
                    (Inside b alpha) 
                )
                (not (On_L a L)) 
                (not (On_L b L)) 
                (not (SameSide a b L))
            )
            (Intersects_LC L alpha)
        )
    )
)

; intersection_circle_line_2
(assert
    (forall ((a Point) (alpha Circle) (L Line))
        (=> 
            (and 
                (Inside a alpha)
                (On_L a L)
            )
            (Intersects_LC L alpha)
        )
    )
) 

; intersection_circle_circle_1
(assert
    (forall ((a Point) (b Point) (alpha Circle) (beta Circle))
        (=> 
            (and 
                (or
                    (On_C a alpha)
                    (Inside a alpha)
                )
                (or 
                    (On_C b alpha)
                    (Inside b alpha)
                )
                (Inside a beta)
                (not (Inside b beta))
                (not (On_C b beta))
            )
            (Intersects_CC alpha beta)
        )
    )
)

; intersection_circle_circle_2
(assert
    (forall ((a Point) (b Point) (alpha Circle) (beta Circle))
        (=> 
            (and 
                (On_C a alpha) 
                (Inside b alpha) 
                (Inside a beta) 
                (On_C b beta)
            )
            (Intersects_CC alpha beta)
        )
    )
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Metric axioms
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; zero_segment_if
(assert
    (forall ((a Point) (b Point)) 
        (=> 
            (= (Segment_PP a b) 0.0) 
            (= a b)
        )
    )
)

; zero_segment_onlyif
(assert
    (forall ((a Point) (b Point)) 
        (=> 
            (= a b)
            (= (Segment_PP a b) 0.0)
        )
    )
)

; segment_gte_zero
(assert
    (forall ((a Point) (b Point)) 
        (>= (Segment_PP a b) 0.0)
    )
)

; segment_symm
(assert
    (forall ((a Point) (b Point)) 
        (= (Segment_PP a b) (Segment_PP b a))
    )
)

; angle_symm
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

; angle_range
(assert
    (forall ((a Point) (b Point) (c Point))
        (=> 
            (and 
                (not (= a b)) 
                (not (= b c))
            )
            (and 
                (>= (Angle_PPP a b c) 0.0) 
                (<= (Angle_PPP a b c) (+ RightAngle RightAngle))
            )
        ) 
    )
)

; degenerated_area
(assert
    (forall ((a Point) (b Point))
        (= (Area_PPP a a b) 0.0)
    )
)

; area_gte_zero
(assert
    (forall ((a Point) (b Point) (c Point))
        (>= (Area_PPP a b c) 0.0)
    )
)

; area_symm_1
(assert
    (forall ((a Point) (b Point) (c Point))
        (= (Area_PPP a b c) (Area_PPP c a b))
    )
)

; area_symm_2
(assert
    (forall ((a Point) (b Point) (c Point))
        (= (Area_PPP a b c) (Area_PPP a c b))
    )
)

; area_congruence
(assert 
    (forall ((a Point) (b Point) (c Point) (d Point) (e Point) (f Point))
        (=>
            (and
                (= (Segment_PP a b) (Segment_PP d e))
                (= (Segment_PP b c) (Segment_PP e f))
                (= (Segment_PP c a) (Segment_PP f d))
                (= (Angle_PPP a b c) (Angle_PPP d e f))
                (= (Angle_PPP b c a) (Angle_PPP e f d))
                (= (Angle_PPP c a b) (Angle_PPP f d e))
            )
            (= (Area_PPP a b c) (Area_PPP d e f))
        )
    )
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Transfer axioms
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; between
(assert
    (forall ((a Point) (b Point) (c Point))
        (=> 
            (Between a b c) 
            (= (+ (Segment_PP a b) (Segment_PP b c)) (Segment_PP a c))
        )
    )
)


; equal_circles
(assert
    (forall ((a Point) (b Point) (c Point) (alpha Circle) (beta Circle))
        (=> 
            (and 
                (Center a alpha) 
                (Center a beta) 
                (On_C b alpha) 
                (On_C c beta)
                (= (Segment_PP a b) (Segment_PP a c))
            )
            (= alpha beta)
        )
    )
)

; point_on_circle_if
(assert
    (forall ((a Point) (b Point) (c Point) (alpha Circle))
        (=> 
            (and 
                (Center a alpha) 
                (On_C b alpha) 
                (= (Segment_PP a c) (Segment_PP a b))
            )
            (On_C c alpha)
        )
    )
)

; point_on_circle_onlyif
(assert
    (forall ((a Point) (b Point) (c Point) (alpha Circle))
        (=> 
            (and 
                (Center a alpha) 
                (On_C b alpha) 
                (On_C c alpha)
                
            )
            (= (Segment_PP a c) (Segment_PP a b))
        )
    )
)

; point_in_circle_if
(assert
    (forall ((a Point) (b Point) (c Point) (alpha Circle))
        (=> 
            (and 
                (Center a alpha) 
                (On_C b alpha)
                (< (Segment_PP a c) (Segment_PP a b)) 
            )
            (Inside c alpha)
        )
    )
)

; point_in_circle_onlyif
(assert
    (forall ((a Point) (b Point) (c Point) (alpha Circle))
        (=> 
            (and 
                (Center a alpha) 
                (On_C b alpha)
                (Inside c alpha)
            )
            (< (Segment_PP a c) (Segment_PP a b)) 
        )
    )
)

; degenerated_angle_if
(assert
    (forall ((a Point) (b Point) (c Point) (L Line))
        (=> 
            (and 
                (not (= a b)) 
                (not (= a c)) 
                (On_L a L) 
                (On_L b L)
                (On_L c L) 
                (not (Between b a c))
            )
            (= (Angle_PPP b a c) 0.0)
        )
    )
)

; degenerated_angle_onlyif
(assert
    (forall ((a Point) (b Point) (c Point) (L Line))
        (=> 
            (and 
                (not (= a b)) 
                (not (= a c)) 
                (On_L a L) 
                (On_L b L)
                (= (Angle_PPP b a c) 0.0)
            )
            (and
                (On_L c L) 
                (not (Between b a c))
            )
        )
    )
)

; angle_superposition
(assert 
    (forall ((a Point) (b Point) (c Point) (d Point) (L Line))
        (=>
            (and
                (On_L a L)
                (On_L b L)
                (not (= a b))
                (not (= d a))
                (= (Angle_PPP b a c) (Angle_PPP b a d))
                (= (Segment_PP a c) (Segment_PP a d))
            )
            (= c d)
        )
    )
)

; sum_angles_if
(assert
    (forall ((a Point) (b Point) (c Point) (d Point) (L Line) (M Line))
        (=> 
            (and 
                (On_L a L) 
                (On_L a M) 
                (On_L b L)
                (On_L c M)
                (not (= a b)) 
                (not (= a c)) 
                (not (On_L d L)) 
                (not (On_L d M)) 
                (not (= L M))
                (= (Angle_PPP b a c) (+ (Angle_PPP b a d) (Angle_PPP d a c)))
            )  
            (and 
                (SameSide b d M) 
                (SameSide c d L)
            )
        )
    )
)

; sum_angles_onlyif
(assert
    (forall ((a Point) (b Point) (c Point) (d Point) (L Line) (M Line))
        (=> 
            (and 
                (On_L a L) 
                (On_L a M) 
                (On_L b L)
                (On_L c M)
                (not (= a b)) 
                (not (= a c)) 
                (not (On_L d L)) 
                (not (On_L d M)) 
                (not (= L M))
                (SameSide b d M) 
                (SameSide c d L)
                
            )  
            (= (Angle_PPP b a c) (+ (Angle_PPP b a d) (Angle_PPP d a c)))
        )
    )
)

; perpendicular_if
(assert
    (forall ((a Point) (b Point) (c Point) (d Point) (L Line))
        (=> 
            (and 
                (On_L a L) 
                (On_L b L) 
                (Between a c b) 
                (not (On_L d L))
                (= (Angle_PPP a c d) (Angle_PPP d c b))
            )   
            (= (Angle_PPP a c d) RightAngle)
        )
    )
)

; perpendicular_onlyif
(assert
    (forall ((a Point) (b Point) (c Point) (d Point) (L Line))
        (=> 
            (and 
                (On_L a L) 
                (On_L b L) 
                (Between a c b) 
                (not (On_L d L))
                (= (Angle_PPP a c d) RightAngle)
            )   
            (= (Angle_PPP a c d) (Angle_PPP d c b))
        )
    )
)

; equal_angles
(assert 
    (forall ((a Point) (b Point) (e Point) (c Point) (f Point) (L Line) (M Line))
        (=>
            (and
                (On_L a L)
                (On_L b L)
                (On_L e L)
                (On_L a M)
                (On_L c M)
                (On_L f M)
                (not (= b a))
                (not (= e a))
                (not (= c a))
                (not (= f a))
                (not (Between b a e))
                (not (Between c a f))
            )
            (= (Angle_PPP b a c) (Angle_PPP e a f))
        )
    )
)

; lines_intersect
(assert 
    (forall ((a Point) (b Point) (c Point) (d Point) (L Line) (M Line) (N Line))
        (=>
            (and
                (On_L a L)
                (On_L b L)
                (On_L b M)
                (On_L c M)
                (On_L c N)
                (On_L d N)
                (not (= b c))
                (SameSide a d M) 
                (< 
                    (+ (Angle_PPP a b c) (Angle_PPP b c d))
                    (+ RightAngle RightAngle)
                )
            )
            (exists ((e Point))
                (and
                    (On_L e L)
                    (On_L e N)
                    (SameSide e a M)
                )
            )
        )
    )
)

; degenerated_area_if
(assert
    (forall ((a Point) (b Point) (c Point) (L Line))
        (=> 
            (and 
                (On_L a L) 
                (On_L b L) 
                (not (= a b))
                (= (Area_PPP a b c) 0.0)
            )    
            (On_L c L)
        )
    )
)

; degenerated_area_onlyif
(assert
    (forall ((a Point) (b Point) (c Point) (L Line))
        (=> 
            (and 
                (On_L a L) 
                (On_L b L) 
                (not (= a b))
                (On_L c L)
            )    
            (= (Area_PPP a b c) 0.0)
        )
    )
)

; sum_areas_if
(assert
    (forall ((a Point) (b Point) (c Point) (d Point) (L Line))
        (=> 
            (and 
                (On_L a L) 
                (On_L b L) 
                (On_L c L) 
                 (not (= a b)) 
                (not (= a c)) 
                (not (= b c))
                (not (On_L d L)) 
                (Between a c b)
            )
            (= 
                (+ (Area_PPP a c d) (Area_PPP d c b)) 
                (Area_PPP a d b)
            )
        )
    )
)

; sum_areas_onlyif
(assert
    (forall ((a Point) (b Point) (c Point) (d Point) (L Line))
        (=> 
            (and 
                (On_L a L) 
                (On_L b L) 
                (On_L c L) 
                 (not (= a b)) 
                (not (= a c)) 
                (not (= b c))
                (not (On_L d L)) 
                (= 
                    (+ (Area_PPP a c d) (Area_PPP d c b)) 
                    (Area_PPP a d b)
                )
            )
            (Between a c b)
        )
    )
)


;(check-sat)
;(get-model)