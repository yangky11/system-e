(*
Transfer inferences defined in Sec. 3.6 of Avigad et al. 2009
*)
Require Import Sorts.

(* diagram-segment transfer axioms *)

(*
1. 
If b is between a and c, then ab + bc = ac.
*)
Axiom between_if : forall (a b c : Point),
    (Between a b c) -> 
        segment2real (SegmentPP a b) + segment2real (SegmentPP b c) = segment2real (SegmentPP a c).
(*
Axiom between_onlyif : forall (a b c : Point), 
    a <> b /\ b <> c /\ c <> a /\
    segment2real (SegmentPP a b) + segment2real (SegmentPP b c) = segment2real (SegmentPP a c) ->
        (Between a b c).
*)

(*
2. 
If a is the center of α and β, b is on α, c is on β, and ab = ac, then α = β.
*)
Axiom equal_circles : forall (a b c : Point) (alpha beta : Circle),
    (a is_center_of alpha) /\ (a is_center_of beta) /\ (b on_circle alpha) /\  
    (c on_circle beta) /\ (SegmentPP a b == SegmentPP a c)%segment ->
        alpha = beta.

(*
3. 
If a is the center of α and b is on α, then ac = ab if and only if c is on α.
*)
Axiom point_on_circle_if : forall (a b c : Point) (alpha : Circle),
    (a is_center_of alpha) /\ (b on_circle alpha) /\ (SegmentPP a c == SegmentPP a b)%segment -> 
        c on_circle alpha.

Axiom point_on_circle_onlyif : forall (a b c : Point) (alpha : Circle),
    (a is_center_of alpha) /\ (b on_circle alpha) /\  (c on_circle alpha) ->
        (SegmentPP a c == SegmentPP a b)%segment.

(*
4. 
If a is the center of α and b is on α, and ac < ab if and only if c is in α.
*)
Axiom point_in_circle_if : forall (a b c : Point) (alpha : Circle),
    (a is_center_of alpha) /\ (b on_circle alpha) /\ (SegmentPP a c < SegmentPP a b)%segment -> 
        c in_circle alpha.

Axiom point_in_circle_onlyif : forall (a b c : Point) (alpha : Circle),
    (a is_center_of alpha) /\ (b on_circle alpha) /\ (c in_circle alpha) ->
        (SegmentPP a c < SegmentPP a b)%segment.

(* diagram-angle transfer axioms *)

(*
1. 
Suppose a != b, a != c, a is on L, and b is on L. Then c is on L and a is
not between b and c if and only if \bac = 0.
*)
Axiom degenerated_angle_if : forall (a b c : Point) (L : Line),
    (a <> b) /\ (a <> c) /\ (a on_line L) /\ (b on_line L) /\ (c on_line L) /\ ~(Between b a c) -> 
        angle2real (AnglePPP b a c) = 0.

Axiom degenerated_angle_onlyif : forall (a b c : Point) (L : Line),
    (a <> b) /\ (a <> c) /\ (a on_line L) /\ (b on_line L) /\ (angle2real (AnglePPP b a c) = 0) ->
        (c on_line L) /\ ~(Between b a c).

(* addtional axiom not in sysetem e *)
Axiom angle_superposition : forall (a b c d : Point) (L : Line), 
    a on_line L /\ b on_line L /\ a <> b /\ d <> a /\ SameSide c d L /\
    (AnglePPP b a c == AnglePPP b a d)%angle /\ 
    (SegmentPP a c == SegmentPP a d)%segment ->
    c = d.

(*
2. 
Suppose a is on L and M, b is on L, c is on M, a != b, a != c, d is not on
L or M, and L != M. Then \bac = \bad + \dac if and only if b and d
are on the same side of M and c and d are on the same side of L.
*)
Axiom sum_angles_if : forall (a b c d : Point) (L M : Line),
    (a on_line L) /\ (a on_line M) /\ (b on_line L) /\ (c on_line M) /\ (a <> b) /\ (a <> c) /\ 
    ~(d on_line L) /\ ~(d on_line M) /\ (L <> M) /\ 
    (angle2real (AnglePPP b a c) = angle2real (AnglePPP b a d) + angle2real (AnglePPP d a c)) -> 
        (SameSide b d M) /\ (SameSide c d L).

Axiom sum_angles_onlyif : forall (a b c d : Point) (L M : Line),
    (a on_line L) /\ (a on_line M) /\ (b on_line L) /\ (c on_line M) /\ (a <> b) /\ (a <> c) /\ 
    ~(d on_line L) /\ ~(d on_line M) /\ (L <> M) /\ (SameSide b d M) /\ (SameSide c d L) ->
        angle2real (AnglePPP b a c) = angle2real (AnglePPP b a d) + angle2real (AnglePPP d a c).

(*
3. 
Suppose a and b are points on L, c is between a and b, and d is not on L.
Then \acd = \dcb if and only if \acd is equal to right-angle.
*)
Axiom perpendicular_if : forall (a b c d : Point) (L : Line),
    (a on_line L) /\ (b on_line L) /\ (Between a c b) /\ ~(d on_line L) /\ (AnglePPP a c d == AnglePPP d c b)%angle -> 
        (AnglePPP a c d == RightAngle)%angle.

Axiom perpendicular_onlyif : forall (a b c d : Point) (L : Line),
    (a on_line L) /\ (b on_line L) /\ (Between a c b) /\ ~(d on_line L) /\ (AnglePPP a c d == RightAngle)%angle ->
        (AnglePPP a c d == AnglePPP d c b)%angle.

Axiom flat_angle_if : forall (a b c : Point), 
    a <> b /\ b <> c /\ (angle2real (AnglePPP a b c) = RightAngle + RightAngle) ->
        (Between a b c).

Axiom flat_angle_onlyif : forall (a b c : Point), 
    (Between a b c) ->
        (angle2real (AnglePPP a b c) = RightAngle + RightAngle).


(*
4. 
Suppose a, b, and b′ are on L, a, c, and c′ are on M, b != a, b′ != a, c != a,
c′ != a, a is not between b and b′, and a is not between c and c′. Then
\bac = \b′ac′.
*)
Axiom equal_angles : forall (a b b' c c' : Point) (L M : Line),
    (a on_line L) /\ (b on_line L) /\ (b' on_line L) /\
    (a on_line M) /\ (c on_line M) /\ (c' on_line M) /\ 
    (b <> a) /\ (b' <> a) /\ (c <> a) /\ (c' <> a) /\ 
    ~(Between b a b') /\ ~(Between c a c') ->
        (AnglePPP b a c == AnglePPP b' a c')%angle.
(* changed!!! *)

(*
5. 
Suppose a and b are on L, b and c are on M, and c and d are on N. Suppose
also that b != c, a and d are on the same side of M, and \abc + \bcd <
right-angle + right-angle. Then L and N intersect, and if e is on L and
N, then e and a are on the same side of M.
*)
Axiom lines_intersect : forall (a b c d : Point) (L M N : Line),
    (a on_line L) /\ (b on_line L) /\ (b on_line M) /\ (c on_line M) /\ 
    (c on_line N) /\ (d on_line N) /\ (b <> c) /\ (SameSide a d M) /\ 
    angle2real (AnglePPP a b c) + angle2real (AnglePPP b c d) < RightAngle + RightAngle ->
        exists e : Point, (e on_line L) /\ (e on_line N) /\ (SameSide e a M).

(* diagram-area transfer axioms *)

(*
1. 
If a and b are on L and a != b, then △abc = 0 if and only if c is on L.
*)
Axiom degenerated_area_if : forall (a b c : Point) (L : Line),
    (a on_line L) /\ (b on_line L) /\ (a <> b) /\ (area2real (AreaPPP a b c) = 0) -> 
        c on_line L.

Axiom degenerated_area_onlyif : forall (a b c : Point) (L : Line),
    (a on_line L) /\ (b on_line L) /\ (a <> b) /\ (c on_line L) ->
        area2real (AreaPPP a b c) = 0.

(*
2. 
If a, b, c are on L and distinct from one another, d is not on L, then c is
between a and b if and only if △acd +△dcb = △adb.
*)
Axiom sum_areas_if : forall (a b c d : Point) (L : Line),
    (a on_line L) /\ (b on_line L) /\ (c on_line L) /\
    (a <> b) /\ (a <> c) /\ (b <> c) /\ ~(d on_line L) /\ (Between a c b) -> 
        area2real (AreaPPP a c d) + area2real (AreaPPP d c b) = area2real (AreaPPP a d b).

Axiom sum_areas_onlyif : forall (a b c d : Point) (L : Line),
    (a on_line L) /\ (b on_line L) /\ (c on_line L) /\
    (a <> b) /\ (a <> c) /\ (b <> c) /\ ~(d on_line L) /\ 
    (area2real (AreaPPP a c d) + area2real (AreaPPP d c b) = area2real (AreaPPP a d b)) ->
        Between a c b.


(* parallelogram rules *)

Axiom parallelogram_area : forall (a b c d : Point) (AB CD AC BD : Line), 
    Parallelogram a b c d AB CD AC BD -> 
        (area2real (AreaPPP a c d) + area2real (AreaPPP a d b) = area2real (AreaPPP b a c) + area2real (AreaPPP b c d)).

Axiom sum_parallelograms_area : forall (a b c d e f : Point) (AB CD AC BD : Line), 
    Parallelogram a b c d AB CD AC BD /\ Between a e b /\ Between c f d ->
        (area2real (AreaPPP a c f) + area2real (AreaPPP a f e) + area2real (AreaPPP e f d) + area2real (AreaPPP e d b) = area2real (AreaPPP a c d) + area2real (AreaPPP a d b)).
