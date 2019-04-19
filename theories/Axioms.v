Declare ML Module "euclid_plugin".

(* Six sorts: point, line, circle, segment, angle, area *)
Require Import Reals.
Open Scope R.

Parameter Point : Set.

Parameter Line : Set.

Parameter Circle : Set.

Inductive Segment : Set :=
| Segment_PP (a b : Point) : Segment.

Parameter segment2real : Segment -> R.
Coercion segment2real_implicit := segment2real.

Bind Scope segment_scope with Segment.
Delimit Scope segment_scope with segment.
Notation "x == y" := (segment2real x = segment2real y) (at level 70, no associativity) : segment_scope.
Notation "x == y == z" := ((segment2real x = segment2real y) /\ (segment2real y = segment2real z)) (at level 70, y at next level) : segment_scope.
Notation "x < y" := (segment2real x < segment2real y) (at level 70, no associativity) : segment_scope.
Notation "x <= y" := (segment2real x <= segment2real y) (at level 70, no associativity) : segment_scope.

Inductive Angle : Set := 
| Angle_PPP (a b c : Point) : Angle
| RightAngle : Angle.

Parameter angle2real : Angle -> R.
Coercion angle2real_implicit := angle2real.

Bind Scope angle_scope with Angle.
Delimit Scope angle_scope with angle.
Notation "x == y" := (angle2real x = angle2real y) (at level 70, no associativity) : angle_scope.
Notation "x == y == z" := ((angle2real x = angle2real y) /\ (angle2real y = angle2real z)) (at level 70, y at next level) : angle_scope.
Notation "x < y" := (angle2real x < angle2real y) (at level 70, no associativity) : angle_scope.
Notation "x <= y" := (angle2real x <= angle2real y) (at level 70, no associativity) : angle_scope.

Inductive Area : Set :=
| Area_PPP (a b c : Point) : Area.

Parameter area2real : Area -> R.
Coercion area2real_implicit := area2real.

Bind Scope area_scope with Area.
Delimit Scope area_scope with area.
Notation "x == y" := (area2real x = area2real y) (at level 70, no associativity) : area_scope.
Notation "x == y == z" := ((area2real x = area2real y) /\ (area2real y = area2real z)) (at level 70, y at next level) : area_scope.
Notation "x < y" := (area2real x < area2real y) (at level 70, no associativity) : area_scope.
Notation "x <= y" := (area2real x <= area2real y) (at level 70, no associativity) : area_scope.

Module DiagrammaticAssertions.

Parameter On_L : Point -> Line -> Prop.
Parameter SameSide : Point -> Point -> Line -> Prop.
Parameter Between : Point -> Point -> Point -> Prop.
Parameter On_C : Point -> Circle -> Prop.
Parameter Inside : Point -> Circle -> Prop.
Parameter Center : Point -> Circle -> Prop.
Parameter Intersects_LL : Line -> Line -> Prop.
Parameter Intersects_LC : Line -> Circle -> Prop.
Parameter Intersects_CC : Circle -> Circle -> Prop.

Notation "a 'on_line' L" := (On_L a L)  (at level 75, no associativity) : assert_scope.
Notation "a 'on_circle' alpha" := (On_C a alpha)  (at level 75, no associativity) : assert_scope.
Notation "a 'in_circle' alpha" := (Inside a alpha)  (at level 75, no associativity) : assert_scope.
Notation "a 'is_center_of' alpha" := (Center a alpha)  (at level 75, no associativity) : assert_scope.
Open Scope assert_scope.

End DiagrammaticAssertions.

Import DiagrammaticAssertions.


(* construction rules *)
Module ConstructionRules.

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

Axiom distinct_point_on_line : forall (L : Line) (a : Point), 
    exists b : Point, (b on_line L) /\ (b <> a).

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

(*
4. 
Let a be a point on L extending the segment from b to c [with a distinct
from. . . ].
Prerequisites: b is on L, c is on L, b != c, [L is distinct from lines . . . ]
Conclusion: a is on L, c is between b and a, [a is distinct from. . . ]
*)
Axiom extending_point : forall (L : Line) (b c : Point),
    (b on_line L) /\ (c on_line L) /\ b <> c -> 
        exists a : Point, (a on_line L) /\ (Between b c a).

Axiom extending_point_not_on_line : forall (L : Line) (b c : Point),
    (b on_line L) /\ (c on_line L) /\ b <> c -> 
        exists a : Point, (a on_line L) /\ (Between b c a).

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
    ~(b on_line L) -> exists a : Point, ~(a on_line L) /\ ~(SameSide a b L).

Axiom distinct_point_opposite_side : forall (L : Line) (b c : Point), 
    ~(b on_line L) -> exists a : Point, a <> c /\ ~(a on_line L) /\ ~(SameSide a b L).

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
    exists a : Point, ~(a on_circle alpha) /\ ~(a in_circle alpha).

Axiom distinct_point_outside_circle : forall (alpha : Circle) (b : Point), 
    exists a : Point, a <> b /\ ~(a on_circle alpha) /\ ~(a in_circle alpha).

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
    Intersects_LL L M -> exists a : Point, (a on_line L) /\ (a on_line M).

(*
2. 
Let a be a point of intersection of α and L.
Prerequisite: α and L intersect
Conclusion: a is on α, a is on L
*)
Axiom intersection_circle_line : forall (alpha : Circle) (L : Line), 
    Intersects_LC L alpha -> exists a : Point, (a on_circle alpha) /\ (a on_line L).

(*
3. 
Let a and b be the two points of intersection of α and L.
Prerequisite: α and L intersect
Conclusion: a is on α, a is on L, b is on α, b is on L, a != b
*)
Axiom intersections_circle_line : forall (alpha : Circle) (L : Line), 
    Intersects_LC L alpha -> exists (a b : Point), 
        (a on_circle alpha) /\ (a on_line L) /\ (b on_circle alpha) /\ (b on_line L) /\ a <> b.

(*
4. 
Let a be the point of intersection of L and α between b and c.
Prerequisites: b is inside α, b is on L, c is not inside α, c is not on α, c is
on L
Conclusion: a is on α, a is on L, a is between b and c
*)
Axiom intersection_circle_line_between_points : forall (alpha : Circle) (L : Line) (b c :Point),
    (b in_circle alpha) /\ (b on_line L) /\ ~(c in_circle alpha) /\ ~(c on_circle alpha) /\ (c on_line L) ->
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
    Intersects_CC alpha beta -> 
        exists a : Point, (a on_circle alpha) /\ (a on_circle beta). 

(*
7. 
Let a and b be the two points of intersection of α and β.
Prerequisite: α and β intersect
Conclusion: a is on α, a is on β, b is on α, b is on β, a != b
*)
Axiom intersections_circles : forall (alpha beta : Circle), 
    Intersects_CC alpha beta -> exists (a b : Point), 
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
    (Intersects_CC alpha beta) /\ (c is_center_of alpha) /\ (d is_center_of beta) /\
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
    (Intersects_CC alpha beta) /\ (c is_center_of alpha) /\ (d is_center_of beta) /\
    (c on_line L) /\ (d on_line L) /\ ~(b on_line L) -> 
        exists a : Point, (a on_circle alpha) /\ (a on_circle beta) /\ ~(SameSide a b L) /\ ~(a on_line L).

End ConstructionRules.


(* diagrammatic inferences *)
Module DiagrammaticInferences.

(* generalities *)

(*
1. 
If a != b, a is on L, and b is on L, a is on M and b is on M, then L = M.
*)
Axiom two_points_determine_line : forall (a b : Point) (L M : Line),
    (a <> b) /\ (a on_line L) /\ (b on_line L) /\ (a on_line M) /\ (b on_line M) -> 
        L = M.

(*
2. 
If a and b are both centers of α then a = b.
*)
Axiom center_unique : forall (a b : Point) (alpha : Circle),
    (a is_center_of alpha) /\ (b is_center_of alpha) -> 
        a = b.

(*
3. 
If a is the center of α then a is inside α.
*)
Axiom center_inside_circle : forall (a : Point) (alpha : Circle),
    a is_center_of alpha -> a in_circle alpha.

(*
4. 
If a is inside α, then a is not on α.
*)
Axiom inside_not_on_circle : forall (a : Point) (alpha : Circle),
    a in_circle alpha -> ~(a on_circle alpha).

(* between axioms *)

(*
1. 
If b is between a and c then b is between c and a, a != b, a != c, and a is 
not between b and c.
*)
Axiom between_symm : forall (a b c : Point), Between a b c -> 
    (Between c b a) /\ (a <> b) /\ (a <> c) /\ ~(Between b a c). 

(*
2. 
If b is between a and c, a is on L, and b is on L, then c is on L.
*)
Axiom between_same_line_c : forall (a b c : Point) (L : Line), 
    (Between a b c) /\ (a on_line L) /\ (b on_line L) -> 
        c on_line L.

(*
3. If b is between a and c, a is on L, and c is on L, then b is on L.
*)
Axiom between_same_line_b : forall (a b c : Point) (L : Line), 
    (Between a b c) /\ (a on_line L) /\ (c on_line L) -> 
        b on_line L.

(*
4. 
If b is between a and c and d is between a and b then d is between a and c.
*)
Axiom between_trans_in : forall (a b c d : Point), 
    (Between a b c) /\ (Between a d b) -> Between a d c.

(*
5. 
If b is between a and c and c is between b and d then b is between a and d.
*)
Axiom between_trans_out : forall (a b c d : Point), 
    (Between a b c) /\ (Between b c d) -> (Between a b d).

(*
6. 
If a, b, and c are distinct points on a line L, then then either b is between
a and c, or a is between b and c, or c is between a and b.
*)
Axiom between_points : forall (a b c : Point) (L : Line), 
    (a <> b) /\ (b <> c) /\ (c <> a) /\ (a on_line L) /\ (b on_line L) /\ (c on_line L) ->
        (Between a b c) \/ (Between b a c) \/ (Between a c b).

(*
7. 
If b is between a and c and b is between a and d then b is not between c
and d.
*)
Axiom between_not_trans : forall (a b c d : Point), 
    (Between a b c) /\ (Between a b d) -> ~(Between c b d).

(* same side axioms *)

(*
1. 
If a is not on L, then a and a are on the same side of L.
*)
Axiom same_side_refl : forall (a : Point) (L : Line), 
    ~(a on_line L) -> SameSide a a L.

(*
2. 
If a and b are on the same side of L, then b and a are on the same side of L.
*)
Axiom same_side_symm : forall (a b : Point) (L : Line), 
    SameSide a b L -> SameSide b a L.

(*
3. 
If a and b are on the same side of L, then a is not on L.
*)
Axiom same_side_not_on_line : forall (a b : Point) (L : Line), 
    SameSide a b L -> ~(a on_line L).

(*
4. 
If a and b are on the same side of L, and a and c are on the same side of
L, then b and c are on the same side of L.
*)
Axiom same_side_trans : forall (a b c : Point) (L : Line), 
    (SameSide a b L) /\ (SameSide a c L) -> SameSide b c L.

(*
5. 
If a, b, and c are not on L, and a and b are not on the same side of L,
then either a and c are on the same side of L, or b and c are on the same
side of L.
*)
Axiom same_side_pigeon_hole : forall (a b c : Point) (L : Line), 
    ~(a on_line L) /\ ~(b on_line L) /\ ~(c on_line L) /\ ~(SameSide a b L) ->
        (SameSide a c L) \/ (SameSide b c L).

(* Pasch axioms *)

(*
1. 
If b is between a and c and a and c are on the same side of L, then a and
b are on the same side of L.
*)
Axiom pasch_1: forall (a b c : Point) (L : Line),
    (Between a b c) /\ (SameSide a c L) -> SameSide a b L.

(*
2. 
If b is between a and c and a is on L and b is not on L, then b and c are
on the same side of L.
*)
Axiom pasch_2: forall (a b c : Point) (L : Line),
    (Between a b c) /\ (a on_line L) /\ ~(b on_line L) -> 
        SameSide b c L.

(* 
3. 
If b is between a and c and b is on L then a and c are not on the same
side of L.
*)
Axiom pasch_3: forall (a b c : Point) (L : Line),
    (Between a b c) /\ (b on_line L) -> ~(SameSide a c L).

(*
4. 
If b is the intersection of distinct lines L and M, a and c are distinct points
on M, a != b, c != b, and a and c are not on the same side of L, then b is
between a and c.
*)
Axiom pasch_4: forall (a b c : Point) (L M : Line),
    (L <> M) /\ (b on_line L) /\ (b on_line M) /\ (a <> c) /\ (a on_line M) /\ 
    (c on_line M) /\ (a <> b) /\ (c <> b) /\ ~(SameSide a c L) -> 
        Between a b c.

(* triple incidence axioms *)

(*
1. 
If L, M, and N are lines meeting at a point a, and b, c, and d are points
on L, M, and N respectively, and if c and d are on the same side of L,
and b and c are on the same side of N, then b and d are not on the same
side of M.
*)
Axiom triple_incidence_1 : forall (L M N : Line) (a b c d : Point),
    (a on_line L) /\ (a on_line M) /\ (a on_line N) /\ (b on_line L) /\ 
    (c on_line M) /\ (d on_line N) /\ (SameSide c d L) /\ (SameSide b c N) -> 
        ~(SameSide b d M).

(*
2. 
If L, M, and N are lines meeting at a point a, and b, c, and d are points
on L, M, and N respectively, and if c and d are on the same side of L,
and b and d are not on the same side of M, and d is not on M and b != a,
then b and c are on the same side of N.
*)
Axiom triple_incidence_2 : forall (L M N : Line) (a b c d : Point),
    (a on_line L) /\ (a on_line M) /\ (a on_line N) /\ (b on_line L) /\ 
    (c on_line M) /\ (d on_line N) /\ (SameSide c d L) /\ ~(SameSide b c N) /\ 
    ~(d on_line M) /\ (b <> a) -> 
        SameSide b c N.

(*
3. 
If L, M, and N are lines meeting at a point a, and b, c, and d are points
on L, M, and N respectively, and if c and d are on the same side of L,
and b and c are on the same side of N, and d and e are on the same side
of M, and c and e are on the same side of N, then c and e are on the same
side of L.
*)
Axiom triple_incidence_3 : forall (L M N : Line) (a b c d e : Point),
    (a on_line L) /\ (a on_line M) /\ (a on_line N) /\ (b on_line L) /\ 
    (c on_line M) /\ (d on_line N) /\ (SameSide c d L) /\ (SameSide b c N) /\ 
    (SameSide d e M) /\ (SameSide c e N) ->
        SameSide c e L.

(* circle axioms *)

(*
1. 
If a, b, and c are on L, a is inside α, b and c are on α, and b != c, then a
is between b and c.
*)
Axiom circle_line_intersections : forall (a b c : Point) (L : Line) (alpha : Circle),
    (a on_line L) /\ (b on_line L) /\ (c on_line L) /\ 
    (a in_circle alpha) /\ (b on_circle alpha) /\ (c on_circle alpha) /\ (b <> c) -> 
        Between b a c.

(*
2. 
If a and b are each inside α or on α, and c is between a and b, then c is
inside α.
*)
Axiom circle_points_between : forall (a b c : Point) (alpha : Circle),
    ((a in_circle alpha) \/ (a on_circle alpha)) /\ 
    ((b in_circle alpha) \/ (b on_circle alpha)) /\ (Between a c b) -> 
        c in_circle alpha.

(*
3. 
If a is inside α or on α, c is not inside α, and c is between a and b, then b
is neither inside α nor on α.
*)
Axiom circle_points_extend : forall (a b c : Point) (alpha : Circle),
    ((a in_circle alpha) \/ (a on_circle alpha)) /\ ~(c in_circle alpha) /\ (Between a c b) -> 
        ~(b in_circle alpha) /\ ~(b on_circle alpha).

(*
4. Let α and β be distinct circles that intersect in distinct points c and d.
Let a be a the center of α, let b be the center of β, and let L be the line
through a and b. Then c and d are not on the same side of L.
*)
Axiom circles_intersections_diff_side : forall (a b c d : Point) (alpha beta : Circle) (L : Line), 
    (alpha <> beta) /\ (c on_circle alpha) /\ (c on_circle beta) /\ (d on_circle alpha) /\ 
    (d on_circle beta) /\ (c <> d) /\ (a is_center_of alpha) /\ (b is_center_of beta) /\ 
    (a on_line L) /\ (b on_line L) ->
        ~(SameSide c d L).

(* intersection rules *)

(*
1. 
If a and b are on different sides of L, and M is the line through a and b,
then L and M intersect.
*)
Axiom intersection_lines: forall (a b : Point) (L M : Line),
    ~(a on_line L) /\ ~(b on_line L) /\ ~(SameSide a b L) /\ (a on_line M) /\ (b on_line M) ->
        Intersects_LL L M.

(*
2. 
If a is on or inside α, b is on or inside α, and a and b are on different sides
of L, then L and α intersect.
*)
Axiom intersection_circle_line_1: forall (a b : Point) (alpha : Circle) (L: Line),
    ((a on_circle alpha) \/ (a in_circle alpha)) /\ ((b on_circle alpha) \/ (b in_circle alpha)) /\ 
    ~(a on_line L) /\ ~(b on_line L) /\ ~(SameSide a b L) -> 
        Intersects_LC L alpha.

(*
3. If a is inside α and on L, then L and α intersect.
*)
Axiom intersection_circle_line_2: forall (a : Point) (alpha : Circle) (L: Line), 
    (a in_circle alpha) /\ (a on_line L) -> Intersects_LC L alpha.

(*
4. If a is on or inside α, b is on or inside α, a is inside β, and b is outside β,
then α and β intersect.
*)
Axiom intersection_circle_circle_1: forall (a b : Point) (alpha beta : Circle), 
    ((a on_circle alpha) \/ (a in_circle alpha)) /\ ((b on_circle alpha) \/ (b in_circle alpha)) /\ 
    (a in_circle beta) /\ ~(b in_circle beta) /\ ~(b on_circle beta) -> 
        Intersects_CC alpha beta.

(*
5. If a is on α, b is in α, a is in β, and b is on β, then α and β intersect.
*)
Axiom intersection_circle_circle_2: forall (a b : Point) (alpha beta : Circle), 
    (a on_circle alpha) /\ (b in_circle alpha) /\ (a in_circle beta) /\ (b on_circle beta) ->
        Intersects_CC alpha beta.

(* equality axioms *)

(*
1. 
x = x
*) 

(*
2. 
If x = y and ϕ(x), then ϕ(y)
*)

End DiagrammaticInferences.


(* Metric Inferences *)


Module MetricInferences.

(* + is associative and commutative, with identity 0. *)

(* < is a linear ordering with least element 0 *)

(* For any x, y, and z, if x < y then x + z < y + z *)

(*
1. 
ab = 0 if and only if a = b.
*)
Axiom zero_segment_if : forall (a b : Point), 
    segment2real (Segment_PP a b) = 0 -> a = b.

Axiom zero_segment_onlyif : forall (a b : Point), 
    a = b -> segment2real (Segment_PP a b) = 0.

(*
2. 
ab ≥ 0
*)
Axiom segment_gte_zero : forall (s : Segment), 0 <= s.

(*
3. 
ab = ba.
*)
Axiom segment_symm : forall (a b : Point), 
    (Segment_PP a b  == Segment_PP b a)%segment.

(*
4. 
a != b and a != c imply \abc = \cba.
*)
Axiom angle_symm : forall (a b c : Point),
    (a <> b) /\ (a <> c) -> (Angle_PPP a b c == Angle_PPP c b a)%angle.

(*
5. 
0 ≤ \abc and \abc ≤ right-angle + right-angle.
*)
Axiom angle_range : forall (ang : Angle),
    (0 <= ang /\ ang <= (RightAngle + RightAngle)%angle).

(*
6. 
△aab = 0.
*)
Axiom degenerated_area : forall (a b : Point), area2real (Area_PPP a a b) = 0.

(*
7. 
△abc ≥ 0.
*)
Axiom area_gte_zero : forall (a : Area), 0 <= a.

(*
8. 
△abc = △cab and △abc = △acb.
*)
Axiom area_symm_1 : forall (a b c : Point),
    (Area_PPP a b c == Area_PPP c a b)%area.

Axiom area_symm_2 : forall (a b c : Point),
    (Area_PPP a b c == Area_PPP a c b)%area.

(*
9. 
If ab = a′b′, bc = b′c′, ca = c′a′, \abc = \a′b′c′, \bca = \b′c′a′, and
\cab = \c′a′b′, then △abc = △a′b′c′.
*)
Axiom area_congruence : forall (a b c a' b' c' : Point),
    (Segment_PP a b == Segment_PP a' b')%segment /\ (Segment_PP b c == Segment_PP b' c')%segment /\ 
    (Segment_PP c a == Segment_PP c' a')%segment /\ (Angle_PPP a b c == Angle_PPP a' b' c')%angle /\ 
    (Angle_PPP b c a == Angle_PPP b' c' a')%angle /\ (Angle_PPP c a b == Angle_PPP c' a' b')%angle /\ 
        (Area_PPP a b c == Area_PPP a' b' c')%area.

End MetricInferences.


(* Transfer Inferences *)
Module TransferInferences.

(* diagram-segment transfer axioms *)

(*
1. 
If b is between a and c, then ab + bc = ac.
*)
Axiom between : forall (a b c : Point),
    (Between a b c) -> 
        segment2real (Segment_PP a b) + segment2real (Segment_PP b c) = segment2real (Segment_PP a c).

(*
2. 
If a is the center of α and β, b is on α, c is on β, and ab = ac, then α = β.
*)
Axiom equal_circles : forall (a b c : Point) (alpha beta : Circle),
    (a is_center_of alpha) /\ (a is_center_of beta) /\ (b on_circle alpha) /\  
    (c on_circle beta) /\ (Segment_PP a b == Segment_PP a c)%segment ->
        alpha = beta.

(*
3. 
If a is the center of α and b is on α, then ac = ab if and only if c is on α.
*)
Axiom point_on_circle_if : forall (a b c : Point) (alpha : Circle),
    (a is_center_of alpha) /\ (b on_circle alpha) /\ (Segment_PP a c == Segment_PP a b)%segment -> 
        c on_circle alpha.

Axiom point_on_circle_onlyif : forall (a b c : Point) (alpha : Circle),
    (a is_center_of alpha) /\ (b on_circle alpha) /\  (c on_circle alpha) ->
        (Segment_PP a c == Segment_PP a b)%segment.

(*
4. 
If a is the center of α and b is on α, and ac < ab if and only if c is in α.
*)
Axiom point_in_circle_if : forall (a b c : Point) (alpha : Circle),
    (a is_center_of alpha) -> (b on_circle alpha) /\ (Segment_PP a c < Segment_PP a b)%segment -> 
        c in_circle alpha.

Axiom point_in_circle_onlyif : forall (a b c : Point) (alpha : Circle),
    (a is_center_of alpha) -> (b on_circle alpha) /\ (c in_circle alpha) ->
        (Segment_PP a c < Segment_PP a b)%segment.

(* diagram-angle transfer axioms *)

(*
1. 
Suppose a != b, a != c, a is on L, and b is on L. Then c is on L and a is
not between b and c if and only if \bac = 0.
*)
Axiom degenerated_angle_if : forall (a b c : Point) (L : Line),
    (a <> b) /\ (a <> c) /\ (a on_line L) /\ (b on_line L) /\ (c on_line L) /\ ~(Between b a c) -> 
        angle2real (Angle_PPP b a c) = 0.

Axiom degenerated_angle_onlyif : forall (a b c : Point) (L : Line),
    (a <> b) /\ (a <> c) /\ (a on_line L) /\ (b on_line L) /\ (angle2real (Angle_PPP b a c) = 0) ->
        (c on_line L) /\ ~(Between b a c).

(*
2. 
Suppose a is on L and M, b is on L, c is on M, a != b, a != c, d is not on
L or M, and L != M. Then \bac = \bad + \dac if and only if b and d
are on the same side of M and c and d are on the same side of L.
*)
Axiom sum_angles_if : forall (a b c d : Point) (L M : Line),
    (a on_line L) /\ (a on_line M) /\ (b on_line L) /\ (c on_line M) /\ (a <> b) /\ (a <> c) /\ 
    ~(d on_line L) /\ ~(d on_line M) /\ (L <> M) /\ 
    (angle2real (Angle_PPP b a c) = angle2real (Angle_PPP b a d) + angle2real (Angle_PPP d a c)) -> 
        (SameSide b d M) /\ (SameSide c d L).

Axiom sum_angles_onlyif : forall (a b c d : Point) (L M : Line),
    (a on_line L) /\ (a on_line M) /\ (b on_line L) /\ (c on_line M) /\ (a <> b) /\ (a <> c) /\ 
    ~(d on_line L) /\ ~(d on_line M) /\ (L <> M) /\ (SameSide b d M) /\ (SameSide c d L) ->
        angle2real (Angle_PPP b a c) = angle2real (Angle_PPP b a d) + angle2real (Angle_PPP d a c).

(*
3. 
Suppose a and b are points on L, c is between a and b, and d is not on L.
Then \acd = \dcb if and only if \acd is equal to right-angle.
*)
Axiom perpendicular_if : forall (a b c d : Point) (L : Line),
    (a on_line L) /\ (b on_line L) /\ (Between a c b) /\ ~(d on_line L) /\ (Angle_PPP a c d == Angle_PPP d c b)%angle -> 
        (Angle_PPP a c d == RightAngle)%angle.

Axiom perpendicular_onlyif : forall (a b c d : Point) (L : Line),
    (a on_line L) /\ (b on_line L) /\ (Between a c b) /\ ~(d on_line L) /\ (Angle_PPP a c d == RightAngle)%angle ->
        (Angle_PPP a c d == Angle_PPP d c b)%angle.

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
        (Angle_PPP b a c == Angle_PPP b' a c')%angle.

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
    angle2real (Angle_PPP a b c) + angle2real (Angle_PPP b c d) < RightAngle + RightAngle ->
        exists e : Point, (e on_line L) /\ (e on_line N) /\ (SameSide e a M).

(* diagram-area transfer axioms *)

(*
1. 
If a and b are on L and a != b, then △abc = 0 if and only if c is on L.
*)
Axiom degenerated_area_if : forall (a b c : Point) (L : Line),
    (a on_line L) /\ (b on_line L) /\ (a <> b) /\ (area2real (Area_PPP a b c) = 0) -> 
        c on_line L.

Axiom degenerated_area_onlyif : forall (a b c : Point) (L : Line),
    (a on_line L) /\ (b on_line L) /\ (a <> b) /\ (c on_line L) ->
        area2real (Area_PPP a b c) = 0.

(*
2. 
If a, b, c are on L and distinct from one another, d is not on L, then c is
between a and b if and only if △acd +△dcb = △adb.
*)
Axiom sum_areas_if : forall (a b c d : Point) (L : Line),
    (a on_line L) /\ (b on_line L) /\ (c on_line L) /\
    (a <> b) /\ (a <> c) /\ (b <> c) /\ ~(d on_line L) /\ (Between a c b) -> 
        area2real (Area_PPP a c d) + area2real (Area_PPP d c b) = area2real (Area_PPP a d b).

Axiom sum_areas_onlyif : forall (a b c d : Point) (L : Line),
    (a on_line L) /\ (b on_line L) /\ (c on_line L) /\
    (a <> b) /\ (a <> c) /\ (b <> c) /\ ~(d on_line L) /\ 
    (area2real (Area_PPP a c d) + area2real (Area_PPP d c b) = area2real (Area_PPP a d b)) ->
        Between a c b.

End TransferInferences.


(* Superposition *)

Require Export Program.Tactics.
Require Export Psatz.

Open Scope segment_scope.

Lemma conj_hyp : forall (P Q R : Prop), P -> (P /\ Q -> R) -> (Q -> R).
Proof.
  auto.
Qed.

Hint Resolve DiagrammaticInferences.intersection_circle_circle_2.
Hint Resolve DiagrammaticInferences.center_inside_circle.

Ltac elim_conj H := 
    match type of H with
    | ?P /\ ?Q -> ?R => match goal with
                                 | [H' : ?P |- _] => replace_hyp H (conj_hyp P Q R H' H)
                                 | _ => fail 2
                                 end
    end.

Ltac euclid_apply' rule name := 
    let lemma := fresh in
    generalize rule; intros lemma;
    repeat match type of lemma with
               | ?P /\ ?Q -> _ => elim_conj lemma
               | forall t : ?T, _ => match goal with
                                            | [ H : ?T |- _ ] => specialize (lemma H)
                                            | _ => let H := fresh in assert (H : T); [ eauto 10; idtac T; fail 3 "unsatisfied hypothesis" |  idtac ]
                                            end
               | exists t : _ , _ => let Hname := fresh "H" name in destruct lemma as [name Hname]; 
                                             match type of Hname with
                                             | _ /\ _ => destruct Hname
                                             end
               | _ /\ _ => destruct lemma
    end.

Tactic Notation "euclid_apply" constr(rule) "as" ident(name) :=
    euclid_apply' rule name.

Tactic Notation "euclid_apply" constr(rule) :=
    let name := fresh "x" in
    euclid_apply' rule name.


