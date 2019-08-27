Require Import Sorts.

(* points *)

(*
1.
Let a be a point [distinct from . . . ].
Prerequisites: none
Conclusion: [a is distinct from. . . ]
*)
Axiom point : exists a : Point, True.

Axiom distinct_point : forall b : Point, exists a : Point, a <> b.

(*
2.
Let a be a point on L [distinct from . . . ].
Prerequisites: [L is distinct from lines. . . ]
Conclusion: a is on L, [a is distinct from. . . ]
*)
Axiom point_on_line : forall L : Line, exists a : Point, a on_line L.

Axiom distinct_point_on_line : forall (L : Line) (b : Point), 
    exists a : Point, (a on_line L) /\ (a <> b).

(*
3.
Let a be a point on L between b and c [distinct from . . . ].
Prerequisites: b is on L, c is on L, b != c, [L is distinct from lines . . . ]
Conclusion: a is on L, a is between b and c, [a is distinct from. . . ]
*)
Axiom point_between_points : forall (L : Line) (b c : Point),
    (b on_line L) /\ (c on_line L) /\ (b <> c) ->
        exists a : Point, (a on_line L) /\ (Between b a c).

Axiom point_between_points_not_on_line : forall (L M : Line) (b c : Point),
    (b on_line L) /\ (c on_line L) /\ b <> c /\ L <> M -> 
        exists a : Point, (a on_line L) /\ (Between b a c) /\ ~(a on_line M).

(* different from the original System E *)
Axiom point_between_points_shorter_than : forall (L : Line) (b c : Point) (s : Segment),
    (b on_line L) /\ (c on_line L) /\ (b <> c) /\ (s > 0) ->
        exists a : Point, (a on_line L) /\ (Between b a c) /\ (SegmentPP b a < s).

(*
4. 
Let a be a point on L extending the segment from b to c [with a distinct
from. . . ].
Prerequisites: b is on L, c is on L, b != c, [L is distinct from lines . . . ]
Conclusion: a is on L, c is between b and a, [a is distinct from. . . ]
*)
Axiom extend_point : forall (L : Line) (b c : Point),
    (b on_line L) /\ (c on_line L) /\ b <> c -> 
        exists a : Point, (a on_line L) /\ (Between b c a).

Axiom extend_point_not_on_line : forall (L M : Line) (b c : Point),
    (b on_line L) /\ (c on_line L) /\ b <> c /\ L <> M -> 
        exists a : Point, (a on_line L) /\ (Between b c a) /\ ~(a on_line M).

Axiom extend_point_longer : forall (L : Line) (b c : Point) (s : Segment),
    (b on_line L) /\ (c on_line L) /\ b <> c -> 
        exists a : Point, (a on_line L) /\ (Between b c a) /\ (SegmentPP c a > s)%segment.

(*
5. 
Let a be a point on the same side of L as b [distinct from. . . ]
Prerequisite: b is not on L
Conclusion: a is on the same side of L as b, [a is distinct from. . . ]
*)
Axiom point_same_side : forall (L : Line) (b : Point), 
    ~(b on_line L) -> exists a : Point, SameSide a b L.


Axiom distinct_point_same_side : forall (L : Line) (b c : Point), 
    ~(b on_line L) -> exists a : Point, a <> c /\ SameSide a b L.

(*
6. 
Let a be a point on the side of L opposite b [distinct from. . . ]
Prerequisite: b is not on L.
Conclusion: a is not on L, a is on the same side of L as b, [a is distinct
from. . . ]
*)
Axiom point_opposite_side : forall (L : Line) (b : Point), 
    ~(b on_line L) -> exists a : Point, OppositeSide a b L.

Axiom distinct_point_opposite_side : forall (L : Line) (b c : Point), 
    ~(b on_line L) -> exists a : Point, a <> c /\ OppositeSide a b L.

(*
7. 
Let a be a point on α [distinct from . . . ].
Prerequisite: [α is distinct from other circles]
Conclusion: a is on α, [a is distinct from. . . ]
*)
Axiom point_on_circle : forall (alpha : Circle), exists a : Point, a on_circle alpha.

Axiom distinct_point_on_circle : forall (alpha : Circle) (b : Point), 
    exists a : Point, a <> b /\ (a on_circle alpha).

(*
8. 
Let a be a point inside α [distinct from . . . ].
Prerequisites: none
Conclusion: a is inside α, [a is distinct from. . . ]
*)
Axiom point_inside_circle : forall (alpha : Circle), exists a : Point, a in_circle alpha.

Axiom distinct_point_inside_circle : forall (alpha : Circle) (b : Point), 
    exists a : Point, a <> b /\ a in_circle alpha.

(*
9. Let a be a point outside α [distinct from . . . ].
Prerequisites: none
Conclusion: a is outside α, [a is distinct from. . . ]
*)
Axiom point_outside_circle : forall (alpha : Circle), 
    exists a : Point, a out_circle alpha.

Axiom distinct_point_outside_circle : forall (alpha : Circle) (b : Point), 
    exists a : Point, a <> b /\ a out_circle alpha.

(* lines and circles *)

(*
1. 
Let L be the line through a and b.
Prerequisite: a != b
Conclusion: a is on L, b is on L
*)
Axiom line_from_points : forall (a b : Point), 
    a <> b -> exists L : Line, (a on_line L) /\ (b on_line L).

(*
2. Let α be the circle with center a passing through b.
Prerequisite: a != b
Conclusion: a is the center of α, b is on α*)
Axiom circle_from_points : forall (a b : Point), 
    a <> b -> exists alpha : Circle, (a is_center_of alpha) /\ (b on_circle alpha).

(* intersections *)

(*
1. 
Let a be the intersection of L and M.
Prerequisite: L and M intersect
Conclusion: a is on L, a is on M
*)
Axiom intersection_lines : forall (L M : Line), 
    IntersectsLL L M -> exists a : Point, (a on_line L) /\ (a on_line M).

(*
2. 
Let a be a point of intersection of α and L.
Prerequisite: α and L intersect
Conclusion: a is on α, a is on L
*)
Axiom intersection_circle_line : forall (alpha : Circle) (L : Line), 
    IntersectsLC L alpha -> exists a : Point, (a on_circle alpha) /\ (a on_line L).

(*
3. 
Let a and b be the two points of intersection of α and L.
Prerequisite: α and L intersect
Conclusion: a is on α, a is on L, b is on α, b is on L, a != b
*)
Axiom intersections_circle_line : forall (alpha : Circle) (L : Line), 
    IntersectsLC L alpha -> exists (a b : Point), 
        (a on_circle alpha) /\ (a on_line L) /\ (b on_circle alpha) /\ (b on_line L) /\ a <> b.

(*
4. 
Let a be the point of intersection of L and α between b and c.
Prerequisites: b is inside α, b is on L, c is not inside α, c is not on α, c is
on L
Conclusion: a is on α, a is on L, a is between b and c
*)
Axiom intersection_circle_line_between_points : forall (alpha : Circle) (L : Line) (b c :Point),
    (b in_circle alpha) /\ (b on_line L) /\ (c out_circle alpha) /\ (c on_line L) ->
        exists a : Point, (a on_circle alpha) /\ (a on_line L) /\ (Between b a c).

(*
5. 
Let a be the point of intersection of L and α extending the segment from
c to b.
Prerequisites: b is inside α, b is on L, c != b, c is on L.
Conclusion: a is on α, a is on L, b is between a and c
*)
Axiom intersection_circle_line_extending_points : forall (alpha : Circle) (L : Line) (b c :Point),
    (b in_circle alpha) /\ (b on_line L) /\ c <> b /\ (c on_line L) ->
        exists a : Point, (a on_circle alpha) /\ (a on_line L) /\ (Between a b c).

(*
6. 
Let a be a point on the intersection of α and β.
Prerequisite: α and β intersect
Conclusion: a is on α, a is on β
*)
Axiom intersection_circles : forall (alpha beta : Circle), 
    IntersectsCC alpha beta -> 
        exists a : Point, (a on_circle alpha) /\ (a on_circle beta). 

(*
7. 
Let a and b be the two points of intersection of α and β.
Prerequisite: α and β intersect
Conclusion: a is on α, a is on β, b is on α, b is on β, a != b
*)
Axiom intersections_circles : forall (alpha beta : Circle), 
    IntersectsCC alpha beta -> exists (a b : Point), 
        (a on_circle alpha) /\ (a on_circle beta) /\ (b on_circle alpha) /\ (b on_circle beta) /\ a <> b.

(*
8.
Let a be the point of intersection of α and β, on the same side of L as b,
where L is the line through their centers, c and d, respectively.
Prerequisites: α and β intersect, c is the center of α, d is the center of β,
c is on L, d is on L, b is not on L
Conclusion: a is on α, a is on β, a and b are on the same side of L
*)
Axiom intersection_same_side : forall (alpha beta : Circle) (b c d : Point) (L : Line),
    (IntersectsCC alpha beta) /\ (c is_center_of alpha) /\ (d is_center_of beta) /\
    (c on_line L) /\ (d on_line L) /\ ~(b on_line L) -> 
        exists a : Point, (a on_circle alpha) /\ (a on_circle beta) /\ (SameSide a b L).

(*
9. 
Let a be the point of intersection of α and β, on the side of L opposite b,
where L is the line through their centers, c and d, respectively.
Prerequisite: α and β intersect, c is the center of α, d is the center of β,
c is on L, d is on L, b is not on L
Conclusion: a is on α, a is on β, a and b are not on the same side of L, a
is not on L.
*)
Axiom intersection_opposite_side : forall (alpha beta : Circle) (b c d : Point) (L : Line),
    (IntersectsCC alpha beta) /\ (c is_center_of alpha) /\ (d is_center_of beta) /\
    (c on_line L) /\ (d on_line L) /\ ~(b on_line L) -> 
        exists a : Point, (a on_circle alpha) /\ (a on_circle beta) /\ OppositeSide a b L.
