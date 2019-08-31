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
            (OnL a L)
        )
    )
)

(assert 
    (forall ((L Line) (a Point))
        (exists ((b Point))
            (and 
                (OnL b L)
                (not (= b a))
            )
        )
    )
)

(assert 
    (forall ((L Line) (b Point) (c Point))
        (=>
            (and
                (OnL b L)
                (OnL c L)
                (not (= b c))
            )
            (exists ((a Point))
                (and
                    (OnL a L)
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
                (OnL b L)
                (OnL c L)
                (not (= b c))
                (not (= L M))
            )
            (exists ((a Point))
                (and
                    (OnL a L)
                    (Between b a c)
                    (not (OnL a M))
                )
            )
        )
    )
)

(assert 
    (forall ((L Line) (b Point) (c Point))
        (=> 
            (and
                (OnL b L)
                (OnL c L)
                (not (= b c))
            )
            (exists ((a Point))
                (and
                    (OnL a L)
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
                (OnL b L)
                (OnL c L)
                (not (= b c))
                (not (= L M))
            )
            (exists ((a Point))
                (and
                    (OnL a L)
                    (Between b c a)
                    (not (OnL a M))
                )
            )
        )
    )
)

(assert 
    (forall ((L Line) (b Point))
        (=>
            (not (OnL b L))
            (exists ((a Point))
                (SameSide a b L)
            )
        )
    )
)

(assert 
    (forall ((L Line) (b Point) (c Point))
        (=>
            (not (OnL b L))
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
            (not (OnL b L))
            (exists ((a Point))
                (and
                    (not (OnL a L))
                    (not (SameSide a b L))
                )
            )
        )
    )
)

(assert 
    (forall ((L Line) (b Point) (c Point))
        (=> 
            (not (OnL b L))
            (exists ((a Point))
                (and
                    (not (= a c))
                    (not (OnL a L))
                    (not (SameSide a b L))
                )
            )
        )
    )
)

(assert 
    (forall ((alpha Circle))
        (exists ((a Point))
            (OnC a alpha)
        )
    )
)

(assert 
    (forall ((alpha Circle) (b Point))
        (exists ((a Point))
            (and
                (not (= a b))
                (OnC a alpha)
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
                (not (OnC a alpha))
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
                (not (OnC a alpha))
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
                    (OnL a L)
                    (OnL b L)
                )
            )
        )
    )
)

; intersections 

(assert 
    (forall ((L Line) (M Line))
        (=>
            (IntersectsLL L M)
            (exists ((a Point))
                (and
                    (OnL a L)
                    (OnL a M)
                )
            )
        )
    )
)

(assert 
    (forall ((alpha Circle) (L Line))
        (=>
            (IntersectsLC L alpha)
            (exists ((a Point))
                (and
                    (OnC a alpha)
                    (OnL a L)
                )
            )
        )
    )
)

(assert 
    (forall ((alpha Circle) (L Line))
        (=>
            (IntersectsLC L alpha)
            (exists ((a Point) (b Point))
                (and
                    (OnC a alpha)
                    (OnL a L)
                    (OnC b alpha)
                    (OnL b L)
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
                (OnL b L)
                (not (Inside c alpha))
                (not (OnC c alpha))
                (OnL c L)
            )
            (exists ((a Point))
                (and
                    (OnC a alpha)
                    (OnL a L)
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
                (OnL b L)
                (not (= c b))
                (OnL c L)
            )
            (exists ((a Point))
                (and
                    (OnC a alpha)
                    (OnL a L)
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
                (OnL b L)
                (not (= c b))
                (OnL c L)
            )
            (exists ((a Point))
                (and
                    (OnC a alpha)
                    (OnL a L)
                    (Between a b c)
                )
            )
        )
    )
)

(assert 
    (forall ((alpha Circle) (beta Circle))
        (=>
            (IntersectsCC alpha beta)
            (exists ((a Point))
                (and
                    (OnC a alpha)
                    (OnC a beta)
                )
            )
        )
    )
)

(assert 
    (forall ((alpha Circle) (beta Circle))
        (=>
            (IntersectsCC alpha beta)
            (exists ((a Point) (b Point))
                (and
                    (OnC a alpha)
                    (OnC a beta)
                    (OnC b alpha)
                    (OnC b beta)
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
                (IntersectsCC alpha beta)
                (Center c alpha)
                (Center c beta)
                (OnL c L)
                (OnL d L)
                (not (OnL b L))
            )
            (exists ((a Point))
                (and
                    (OnC a alpha)
                    (OnC a beta)
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
                (IntersectsCC alpha beta)
                (Center c alpha)
                (Center c beta)
                (OnL c L)
                (OnL d L)
                (not (OnL b L))
            )
            (exists ((a Point))
                (and
                    (OnC a alpha)
                    (OnC a beta)
                    (not (SameSide a b L))
                    (not (OnL a L))
                )
            )
        )
    )
)