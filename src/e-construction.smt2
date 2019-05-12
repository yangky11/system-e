;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Construction rules
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; points

(assert 
    (exists ((a Point)) 
        true
    )
)

(assert 
    (forall ((a Point))
        (exists ((b Point))
            (not (= b a))
        )
    )
)

(assert 
    (forall ((L Line))
        (exists ((a Point))
            (On_L a L)
        )
    )
)

(assert 
    (forall ((L Line) (a Point))
        (exists ((b Point))
            (and 
                (On_L b L)
                (not (= b a))
            )
        )
    )
)

(assert 
    (forall ((L Line) (b Point) (c Point))
        (=>
            (and
                (On_L b L)
                (On_L c L)
                (not (= b c))
            )
            (exists ((a Point))
                (and
                    (On_L a L)
                    (Between b a c)
                )
            )
        )
    )
)

(assert 
    (forall ((L Line) (M Line) (b Point) (c Point))
        (=>
            (and
                (On_L b L)
                (On_L c L)
                (not (= b c))
                (not (= L M))
            )
            (exists ((a Point))
                (and
                    (On_L a L)
                    (Between b a c)
                    (not (On_L a M))
                )
            )
        )
    )
)

(assert 
    (forall ((L Line) (b Point) (c Point))
        (=> 
            (and
                (On_L b L)
                (On_L c L)
                (not (= b c))
            )
            (exists ((a Point))
                (and
                    (On_L a L)
                    (Between b c a)
                )
            )
        )
    )
)

(assert 
    (forall ((L Line) (M Line) (b Point) (c Point))
        (=> 
            (and
                (On_L b L)
                (On_L c L)
                (not (= b c))
                (not (= L M))
            )
            (exists ((a Point))
                (and
                    (On_L a L)
                    (Between b c a)
                    (not (On_L a M))
                )
            )
        )
    )
)

(assert 
    (forall ((L Line) (b Point))
        (=>
            (not (On_L b L))
            (exists ((a Point))
                (SameSide a b L)
            )
        )
    )
)

(assert 
    (forall ((L Line) (b Point) (c Point))
        (=>
            (not (On_L b L))
            (exists ((a Point))
                (and
                    (not (= a c))
                    (SameSide a b L)
                )
            )
        )
    )
)

(assert 
    (forall ((L Line) (b Point))
        (=> 
            (not (On_L b L))
            (exists ((a Point))
                (and
                    (not (On_L a L))
                    (not (SameSide a b L))
                )
            )
        )
    )
)

(assert 
    (forall ((L Line) (b Point) (c Point))
        (=> 
            (not (On_L b L))
            (exists ((a Point))
                (and
                    (not (= a c))
                    (not (On_L a L))
                    (not (SameSide a b L))
                )
            )
        )
    )
)

(assert 
    (forall ((alpha Circle))
        (exists ((a Point))
            (On_C a alpha)
        )
    )
)

(assert 
    (forall ((alpha Circle) (b Point))
        (exists ((a Point))
            (and
                (not (= a b))
                (On_C a alpha)
            )
        )
    )
)

(assert 
    (forall ((alpha Circle))
        (exists ((a Point))
            (Inside a alpha)
        )
    )
)

(assert 
    (forall ((alpha Circle) (b Point))
        (exists ((a Point))
            (and
                (not (= a b))
                (Inside a alpha)
            )
        )
    )
)

(assert 
    (forall ((alpha Circle))
        (exists ((a Point))
            (and
                (not (On_C a alpha))
                (not (Inside a alpha))
            )
        )
    )
)

(assert 
    (forall ((alpha Circle) (b Point))
        (exists ((a Point))
            (and
                (not (= a b))
                (not (On_C a alpha))
                (not (Inside a alpha))
            )
        )
    )
)

(assert 
    (forall ((a Point) (b Point))
        (=>
            (not (= a b))
            (exists ((L Line))
                (and
                    (On_L a L)
                    (On_L b L)
                )
            )
        )
    )
)

; intersections 

(assert 
    (forall ((L Line) (M Line))
        (=>
            (Intersects_LL L M)
            (exists ((a Point))
                (and
                    (On_L a L)
                    (On_L a M)
                )
            )
        )
    )
)

(assert 
    (forall ((alpha Circle) (L Line))
        (=>
            (Intersects_LC L alpha)
            (exists ((a Point))
                (and
                    (On_C a alpha)
                    (On_L a L)
                )
            )
        )
    )
)

(assert 
    (forall ((alpha Circle) (L Line))
        (=>
            (Intersects_LC L alpha)
            (exists ((a Point) (b Point))
                (and
                    (On_C a alpha)
                    (On_L a L)
                    (On_C b alpha)
                    (On_L b L)
                    (not (= a b))
                )
            )
        )
    )
)

(assert 
    (forall ((alpha Circle) (L Line) (b Point) (c Point))
        (=>
            (and
                (Inside b alpha)
                (On_L b L)
                (not (Inside c alpha))
                (not (On_C c alpha))
                (On_L c L)
            )
            (exists ((a Point))
                (and
                    (On_C a alpha)
                    (On_L a L)
                    (Between b a c)
                )
            )
        )
    )
)

(assert 
    (forall ((alpha Circle) (L Line) (b Point) (c Point))
        (=>
            (and
                (Inside b alpha)
                (On_L b L)
                (not (= c b))
                (On_L c L)
            )
            (exists ((a Point))
                (and
                    (On_C a alpha)
                    (On_L a L)
                    (Between a b c)
                )
            )
        )
    )
)

(assert 
    (forall ((alpha Circle) (L Line) (b Point) (c Point))
        (=>
            (and
                (Inside b alpha)
                (On_L b L)
                (not (= c b))
                (On_L c L)
            )
            (exists ((a Point))
                (and
                    (On_C a alpha)
                    (On_L a L)
                    (Between a b c)
                )
            )
        )
    )
)

(assert 
    (forall ((alpha Circle) (beta Circle))
        (=>
            (Intersects_CC alpha beta)
            (exists ((a Point))
                (and
                    (On_C a alpha)
                    (On_C a beta)
                )
            )
        )
    )
)

(assert 
    (forall ((alpha Circle) (beta Circle))
        (=>
            (Intersects_CC alpha beta)
            (exists ((a Point) (b Point))
                (and
                    (On_C a alpha)
                    (On_C a beta)
                    (On_C b alpha)
                    (On_C b beta)
                    (not (= a b))
                )
            )
        )
    )
)

(assert 
    (forall ((alpha Circle) (beta Circle) (b Point) (c Point) (d Point) (L Line))
        (=>
            (and
                (Intersects_CC alpha beta)
                (Center c alpha)
                (Center c beta)
                (On_L c L)
                (On_L d L)
                (not (On_L b L))
            )
            (exists ((a Point))
                (and
                    (On_C a alpha)
                    (On_C a beta)
                    (SameSide a b L)
                )
            )
        )
    )
)

(assert 
    (forall ((alpha Circle) (beta Circle) (b Point) (c Point) (d Point) (L Line))
        (=>
            (and
                (Intersects_CC alpha beta)
                (Center c alpha)
                (Center c beta)
                (On_L c L)
                (On_L d L)
                (not (On_L b L))
            )
            (exists ((a Point))
                (and
                    (On_C a alpha)
                    (On_C a beta)
                    (not (SameSide a b L))
                    (not (On_L a L))
                )
            )
        )
    )
)