(benchmark e
   :source { A formalization of Euclidean geometry }
   :logic AUFLIRA
   :category { crafted }
;   :difficulty { 5 }
;   :status unsat
   :extrasorts (Point)
   :extrasorts (Line)
   :extrasorts (Circle)
   :extrapreds ((bet Point Point Point))
   :extrapreds ((on Point Line))
   :extrapreds ((onc Point Circle))
   :extrapreds ((in Point Circle))
   :extrapreds ((center Point Circle))
   :extrapreds ((sameside Point Point Line))
   :extrapreds ((intersects Line Line))
   :extrapreds ((intersectslc Line Circle))
   :extrapreds ((intersectscc Circle Circle))
   :extrafuns  ((seg Point Point Real))
   :extrafuns  ((angle Point Point Point Real))
   :extrafuns  ((area Point Point Point Real))
   :extrafuns  ((rightangle Real))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Diagrammatic axioms
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;
; Generalities
;

; Two points determine a line
:assumption
(forall (?a Point) (?b Point) (?L Line) (?M Line)
  (implies (and (not (= ?a ?b)) (on ?a ?L) (on ?b ?L)
      (on ?a ?M) (on ?b ?M))
    (= ?L ?M)))

; Center is unique
:assumption
(forall (?a Point) (?b Point) (?C Circle)
  (implies (and (center ?a ?C) (center ?b ?C))
    (= ?a ?b)))

:assumption
(forall (?a Point) (?C Circle)
  (implies (center ?a ?C) (in ?a ?C)))

;
; Between axioms
;

:assumption
(forall (?a Point) (?b Point) (?c Point)
  (implies (bet ?a ?b ?c)
    (and (bet ?c ?b ?a) (not (= ?a ?b)) (not (= ?a ?c))
      (not (bet ?b ?a ?c)))))

:assumption
(forall (?a Point) (?b Point) (?c Point) (?L Line)
   (implies (and (bet ?a ?b ?c) (on ?a ?L) (on ?b ?L)) (on ?c ?L)))

:assumption
(forall (?a Point) (?b Point) (?c Point) (?L Line)
  (implies (and (bet ?a ?b ?c) (on ?a ?L) (on ?c ?L)) (on ?b ?L)))

:assumption
(forall (?a Point) (?b Point) (?c Point) (?d Point)
  (implies (and (bet ?a ?b ?c) (bet ?a ?d ?b))
    (bet ?a ?d ?c)))
;   (and (bet ?a ?d ?c) (bet ?d ?b ?c))))    This variant redundant.

:assumption
(forall (?a Point) (?b Point) (?c Point) (?d Point)
  (implies (and (bet ?a ?b ?c) (bet ?b ?c ?d))
    (bet ?a ?b ?d)))
;   (and (bet ?a ?c ?d) (bet ?a ?b ?d))))    This variant redundant.

:assumption
(forall (?a Point) (?b Point) (?c Point) (?L Line)
   (implies (and (on ?a ?L) (on ?b ?L) (on ?c ?L)
       (not (= ?a ?b)) (not (= ?a ?c)) (not (= ?b ?c)))
     (or (bet ?a ?b ?c) (bet ?b ?a ?c) (bet ?a ?c ?b))))

; This one is a first-order consequence of the others
; :assumption
; (forall (?a Point) (?b Point) (?c Point) (?d Point)
;     (implies (and (bet ?a ?b ?c) (bet ?a ?b ?d)) 
;       (not (bet ?d ?b ?c))))

;
; Same side axioms
;

:assumption
(forall (?a Point) (?L Line)
   (implies (not (on ?a ?L)) (sameside ?a ?a ?L)))

:assumption
(forall (?a Point) (?b Point) (?L Line)
   (implies (sameside ?a ?b ?L)
     (and (not (on ?a ?L)) (sameside ?b ?a ?L))))

:assumption
(forall (?a Point) (?b Point) (?c Point) (?L Line)
   (implies (and (sameside ?a ?b ?L) (sameside ?a ?c ?L))
     (sameside ?b ?c ?L)))

:assumption
(forall (?a Point) (?b Point) (?c Point) (?L Line)
   (implies (and (not (on ?a ?L)) (not (on ?b ?L)) (not (on ?c ?L)))
     (or (sameside ?a ?b ?L) (sameside ?a ?c ?L) (sameside ?b ?c ?L))))

; definition of diff-side
; (forall (?a Point) (?b Point) (?L Line)
;   (= (diff-side ?a ?b ?L)
;     (and (not (on ?a ?L)) (not (on ?b ?L))
;       (not (sameside ?a ?b ?L)))))

;
; Pasch axioms
;

:assumption
(forall (?a Point) (?b Point) (?c Point) (?L Line)
   (implies (and (bet ?a ?b ?c) (sameside ?a ?c ?L))
     (sameside ?a ?b ?L)))
;    (and (sameside ?a ?b ?L) (sameside ?b ?c ?L)))) This variant redundant

:assumption
(forall (?a Point) (?b Point) (?c Point) (?L Line)
   (implies (and (bet ?a ?b ?c) (on ?a ?L) (not (on ?b ?L)))
     (sameside ?b ?c ?L)))

:assumption
(forall (?a Point) (?b Point) (?c Point) (?L Line)
   (implies (and (bet ?a ?b ?c) (on ?b ?L))
     (not (sameside ?a ?c ?L))))

:assumption
(forall (?a Point) (?b Point) (?c Point) (?L Line) (?M Line)
   (implies (and (not (= ?a ?b)) (not (= ?b ?c)) (not (= ?L ?M)) (on ?a ?M)
       (on ?b ?M) (on ?c ?M)
     (not (sameside ?a ?c ?L)) (on ?b ?L))
       (bet ?a ?b ?c)))

;
; Triple incidence axioms
;

:assumption
(forall (?a Point) (?b Point) (?c Point) (?d Point)
    (?L Line) (?M Line) (?N Line)
  (implies (and (on ?a ?L) (on ?a ?M) (on ?a ?N) 
      (on ?b ?L) (on ?c ?M) (on ?d ?N) 
      (sameside ?c ?d ?L) (sameside ?b ?c ?N))
    (not (sameside ?b ?d ?M))))

:assumption
(forall (?a Point) (?b Point) (?c Point) (?d Point)
    (?L Line) (?M Line) (?N Line)
   (implies (and (on ?a ?L) (on ?a ?M) (on ?a ?N) 
       (on ?b ?L) (on ?c ?M) (on ?d ?N)
       (sameside ?c ?d ?L)
       (not (sameside ?d ?b ?M)) (not (on ?d ?M)) (not (= ?b ?a)))
     (sameside ?b ?c ?N)))

:assumption
(forall (?a Point) (?b Point) (?c Point) (?d Point) (?e Point)
    (?L Line) (?M Line) (?N Line)
  (implies (and (on ?a ?L) (on ?a ?M) (on ?a ?N) 
      (on ?b ?L) (on ?c ?M) (on ?d ?N) 
      (sameside ?b ?c ?N) (sameside ?d ?c ?L)
      (sameside ?d ?e ?M) (sameside ?c ?e ?N))
    (sameside ?c ?e ?L)))

; this follows from the others
;:assumption
;(forall (?a Point) (?b Point) (?c Point) (?d Point) (?e Point)
;    (?L Line) (?M Line) (?N Line)
;  (implies (and (on ?a ?L) (on ?a ?M) (on ?a ?N) 
;      (on ?b ?L) (on ?c ?M) (on ?d ?N)
;      (sameside ?d ?c ?L) 
;      (not (sameside ?d ?b ?M)) (not (on ?d ?M)) (not (= ?b ?a))
;      (sameside ?d ?e ?M) (sameside ?c ?e ?N))
;    (sameside ?e ?c ?L)))

;
; Circle axioms
;

:assumption
(forall (?a Point) (?b Point) (?c Point) (?C Circle) (?L Line)
  (implies (and (in ?a ?C) (onc ?b ?C) (onc ?c ?C) (on ?a ?L)
      (on ?b ?L) (on ?c ?L) (not (= ?b ?c)))
    (bet ?b ?a ?c)))

:assumption
(forall (?a Point) (?b Point) (?c Point) (?C Circle)
  (implies (and (or (in ?a ?C) (onc ?a ?C))
      (or (in ?b ?C) (onc ?b ?C))
      (bet ?a ?c ?b))
  (in ?c ?C)))

:assumption
(forall (?a Point) (?b Point) (?c Point) (?C Circle) (?L Line)
   (implies (and (or (in ?a ?C) (onc ?a ?C)) (not (in ?c ?C)) 
       (bet ?a ?c ?b))
     (and (not (in ?b ?C)) (not (onc ?b ?C)))))

:assumption
(forall (?a Point) (?b Point) (?c Point) (?d Point)
     (?C Circle) (?D Circle) (?L Line)
   (implies (and (onc ?c ?C) (onc ?c ?D) (onc ?d ?C) (onc ?d ?D) 
       (not (= ?C ?D)) (not (= ?c ?d))
       (on ?a ?L) (on ?b ?L) (center ?a ?C) (center ?a ?D))
     (not (sameside ?c ?d ?L))))

;
; Intersections
;

:assumption
(forall (?L Line) (?M Line) (?a Point) (?b Point)
    (implies (and (on ?a ?M) (on ?b ?M) (not (sameside ?a ?b ?L)))
      (intersects ?L ?M)))

:assumption
(forall (?C Circle) (?L Line) (?a Point) (?b Point)
    (implies (and (or (in ?a ?C) (onc ?a ?C)) (or (in ?b ?C) (onc ?b ?C))
        (not (on ?a ?L)) (not (on ?b ?L)) (not (sameside ?a ?b ?L)))
      (intersectslc ?L ?C)))

:assumption
(forall (?L Line) (?C Circle) (?a Point)
    (implies (and (in ?a ?C) (on ?a ?L))
      (intersectslc ?L ?C)))

:assumption
(forall (?C Circle) (?D Circle) (?a Point) (?b Point)
    (implies (and (onc ?a ?C) (or (in ?b ?C) (onc ?b ?C))
        (in ?a ?D) (not (in ?b ?D)) (not (onc ?b ?D)))
      (intersectscc ?C ?D)))

:assumption
(forall (?C Circle) (?D Circle) (?a Point) (?b Point)
    (implies (and (onc ?a ?C) (in ?b ?D) (in ?a ?D) (onc ?b ?D))
      (intersectscc ?C ?D)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Metric axioms
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; segments

:assumption
(forall (?a Point) (?b Point) (implies (= (seg ?a ?b) 0.0) (= ?a ?b)))

:assumption
(forall (?a Point) (= (seg ?a ?a) 0.0))

:assumption
(forall (?a Point) (?b Point) (>= (seg ?a ?b) 0.0))

:assumption
(forall (?a Point) (?b Point) (= (seg ?a ?b) (seg ?b ?a)))

; angles

:assumption
(forall (?a Point) (?b Point) (?c Point)
  (implies (and (not (= ?a ?b)) (not (= ?b ?c)))
    (= (angle ?a ?b ?c) (angle ?c ?b ?a))))

:assumption
(forall (?a Point) (?b Point) (?c Point)
  (implies (and (not (= ?a ?b)) (not (= ?b ?c)))
    (and (>= (angle ?a ?b ?c) 0.0) 
         (<= (angle ?a ?b ?c) (+ rightangle rightangle)))))

; areas

:assumption
(forall (?a Point) (?b Point)
  (= (area ?a ?a ?b) 0.0))

:assumption
(forall (?a Point) (?b Point) (?c Point)
  (>= (area ?a ?b ?c) 0.0))

:assumption
(forall (?a Point) (?b Point) (?c Point)
  (and (= (area ?a ?b ?c) (area ?c ?a ?b)) 
    (= (area ?a ?b ?c) (area ?b ?a ?c))))

; congruent triangles have same area
;:assumption
;(forall (?a Point) (?b Point) (?c Point) (?d Point) (?e Point) (?f Point)
;  (implies (and (= (seg ?a ?b) (seg ?d ?e)) (= (seg ?b ?c) (seg ?e ?f))
;      (= (seg ?c ?a) (seg ?f ?d)) (= (angle ?a ?b ?c) (angle ?d ?e ?f))
;      (= (angle ?b ?c ?a) (angle ?e ?f ?d)) 
;      (= (angle ?c ?a ?b) (angle ?f ?d ?e)))
;    (= (area ?a ?b ?c) (area ?d ?e ?f))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Transfer axioms
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;
; Diagram-segment transfer axioms
;

:assumption
(forall (?a Point) (?b Point) (?c Point)
  (implies (bet ?a ?b ?c) (= (+ (seg ?a ?b) (seg ?b ?c)) (seg ?a ?c))))

; center and radius determines the circle
:assumption
(forall (?a Point) (?b Point) (?c Point) (?C Circle) (?D Circle)
  (implies (and (center ?a ?C) (center ?a ?D) (onc ?b ?C) (onc ?c ?D)
      (= (seg ?a ?b) (seg ?a ?c)))
    (= ?C ?D)))

:assumption
(forall (?a Point) (?b Point) (?c Point) (?C Circle)
  (implies (and (center ?a ?C) (onc ?b ?C) (= (seg ?a ?c) (seg ?a ?b)))
         (onc ?c ?C)))

:assumption
(forall (?a Point) (?b Point) (?c Point) (?C Circle)
  (implies (and (center ?a ?C) (onc ?b ?C))
      (= (< (seg ?a ?c) (seg ?a ?b))
         (in ?c ?C))))

;
; Diagram-angle transfer axioms
;

; colinear iff angle is equal to 0
:assumption
(forall (?a Point) (?b Point) (?c Point) (?L Line)
  (implies (and (not (= ?a ?b)) (not (= ?a ?c)) (on ?a ?L) (on ?b ?L))
    (= (and (on ?c ?L) (not (bet ?c ?a ?b)))       
       (= (angle ?b ?a ?c) 0.0) )))

; follows from previous if a and b are both on some line, L
; :assumption
; (forall (?a Point) (?b Point)
;   (implies (not (= ?a ?b)) (= (angle ?a ?b ?a) 0.0)))

; follows from previous axioms
; not colinear iff angle > 0
;:assumption
;(forall (?a Point) (?b Point) (?c Point) (?L Line)
; (implies (and (not (= ?a ?b)) (not (= ?b ?c)) (on ?a ?L) (on ?b ?L))
;   (= (or (not (on ?c ?L) (bet ?c ?a ?b)))
;      (> (angle ?a ?b ?c) 0.0))))

; point inside angle iff angles sum
:assumption
(forall (?a Point) (?b Point) (?c Point) (?d Point) (?L Line) (?M Line)
  (implies (and (on ?a ?L) (on ?b ?L) (on ?a ?M) (on ?c ?M)
      (not (= ?a ?b)) (not (= ?a ?c)) (not (on ?d ?L)) (not (on ?d ?M)) 
      (not (= ?L ?M)))
  (= (= (angle ?b ?a ?c) (+ (angle ?b ?a ?d) (angle ?d ?a ?c)))
     (and (sameside ?b ?d ?M) (sameside ?d ?c ?L)))))

; def right angle (and all right angles are equal)
:assumption
(forall (?a Point) (?b Point) (?c Point) (?d Point) (?L Line)
  (implies (and (on ?a ?L) (on ?b ?L) (bet ?a ?c ?b) (not (on ?d ?L)))
    (= (= (angle ?a ?c ?d) (angle ?d ?c ?b))
       (= (angle ?a ?c ?d) rightangle))))

; alternate descriptions of the same angle are equal
;:assumption
;(forall (?a Point) (?b Point) (?c Point) (?d Point) (?e Point) 
;    (?L Line) (?M Line)
;  (implies (and (on ?a ?L) (on ?b ?L) (on ?d ?L) 
;                  (not (= ?a ?b)) (not (= ?a ?d))
;                (on ?a ?M) (on ?c ?M) (on ?e ?M)
;                  (not (= ?a ?c)) (not (= ?a ?e))
;                (not (bet ?b ?a ?d)) (not (bet ?c ?a ?e)))
;    (= (angle ?b ?a ?c) (angle ?d ?a ?e))))
               
; the parallel postulate
;:assumption
;(forall (?a Point) (?b Point) (?c Point) (?d Point) (?e Point) 
;    (?L Line) (?M Line) (?N Line)
;  (implies (and (on ?a ?L) (on ?b ?L) (on ?b ?M) (on ?c ?M) (on ?c ?N)
;      (on ?d ?M) (not (= ?b ?c)) (sameside ?a ?d ?N)
;      (< (+ (angle ?a ?b ?c) (angle ?b ?c ?d)) 
;         (+ rightangle rightangle)))
;    (and (intersects ?L ?N)
;         (implies (and (on ?e ?L) (on ?e ?N)) (sameside ?e ?a ?M )))))

;
; Diagram / areas
;

:assumption 
(forall (?a Point) (?b Point) (?c Point) (?L Line)
  (implies (and (on ?a ?L) (on ?b ?L) (not (= ?a ?b)))
    (= (= (area ?a ?b ?c) 0.0)
       (on ?c ?L))))

; areas sum
:assumption
(forall (?a Point) (?b Point) (?c Point) (?d Point) (?L Line)
  (implies (and (on ?a ?L) (on ?b ?L) (on ?c ?L) (not (on ?d ?L)) 
      (not (= ?a ?b)) (not (= ?c ?a)) (not (= ?c ?b)))
    (= (bet ?a ?c ?b)
       (= (+ (area ?a ?c ?d) (area ?d ?c ?b)) (area ?a ?d ?b)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Test diagram
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;
; make some points and lines
;

:extrafuns ((p Point))
:extrafuns ((q Point))
:extrafuns ((r Point))
:extrafuns ((s Point))
:extrafuns ((t Point))
:extrafuns ((u Point))
:extrafuns ((v Point))
:extrafuns ((K Line))
:extrafuns ((L Line))
:extrafuns ((M Line))
:extrafuns ((N Line))
:extrafuns ((O Line))

;
; describe the diagram
;

:assumption (on p L)
:assumption (on q L)
:assumption (on p N)
:assumption (on s N)
:assumption (on t N)
:assumption (on p M)
:assumption (on r M)
:assumption (on q O)
:assumption (on s O)
:assumption (on r O)
:assumption (on q K)
:assumption (on t K)
:assumption (not (on r L))
:assumption (bet p s t)
:assumption (bet q s r)
:assumption (bet s u t)
:assumption (not (= p q))
:assumption (bet p q v)

; satisfiable

; :formula (true)
; :formula (not (sameside s t O))
; :formula (sameside u t M)

; unsatisfiable

:formula (sameside p t O)
:formula (sameside s t O)
:formula (not (sameside s t M))
:formula (not (sameside u t M))
:formula (bet s p t)
:formula (= M N)
:formula (bet q s u)
:formula (on q N)
:formula (= q t)
:formula (not (< (seg s u) (seg s t)))
:formula (not (< (seg u s) (seg s t)))
:formula (not (< (+ (seg s u) (seg u t)) (seg p t)))
:formula (not (< (+ (seg u s) (seg u t)) (seg p t)))
:formula (on u L)
:formula (on t L)
:formula (on p K)
:formula (not (sameside r s L))
:formula (not (sameside s u L))

; takes a few of seconds
:formula (not (sameside r u L))

:formula (sameside s v K)
:formula (not (= (+ (angle r p s) (angle s p q)) (angle r p q)))
:formula (not (sameside p s K))
:formula (not (sameside s t L))
:formula (= L K)
:formula (= q s)
:formula (= q t)
:formula (= q p)

; this one takes a long time
; :formula (not (= (+ (angle p q s) (angle s q t)) (angle p q t)))

; this one takes a long time
; :formula (not (< (angle p q s) (angle p q t)))

; immediate
; :formula (not (implies
;   (= (+ (angle p q s) (angle s q t)) (angle p q t))
;     (< (angle p q s) (angle p q t))))

)
