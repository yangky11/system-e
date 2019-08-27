Require Import Sorts.

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
    ~(a on_line L) /\ ~(b on_line L) /\ ~(c on_line L) ->
        (SameSide a b L) \/ (SameSide a c L) \/ (SameSide b c L).

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
    (c on_line M) /\ (d on_line N) /\ (SameSide c d L) /\ ~(SameSide b d M) /\ 
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
        IntersectsLL L M.

Axiom intersection_lines_common_point : forall (a : Point) (L M : Line),
    a on_line L /\ a on_line M /\ L <> M ->
        IntersectsLL L M.

Axiom intersection_symm : forall (L M : Line), IntersectsLL L M -> IntersectsLL M L.

(*
2. 
If a is on or inside α, b is on or inside α, and a and b are on different sides
of L, then L and α intersect.
*)
Axiom intersection_circle_line_1: forall (a b : Point) (alpha : Circle) (L: Line),
    ((a on_circle alpha) \/ (a in_circle alpha)) /\ ((b on_circle alpha) \/ (b in_circle alpha)) /\ 
    ~(a on_line L) /\ ~(b on_line L) /\ ~(SameSide a b L) -> 
        IntersectsLC L alpha.

(*
3. If a is inside α and on L, then L and α intersect.
*)
Axiom intersection_circle_line_2: forall (a : Point) (alpha : Circle) (L: Line), 
    (a in_circle alpha) /\ (a on_line L) -> IntersectsLC L alpha.

(*
4. If a is on or inside α, b is on or inside α, a is inside β, and b is outside β,
then α and β intersect.
*)
Axiom intersection_circle_circle_1: forall (a b : Point) (alpha beta : Circle), 
    ((a on_circle alpha) \/ (a in_circle alpha)) /\ ((b on_circle alpha) \/ (b in_circle alpha)) /\ 
    (a in_circle beta) /\ ~(b in_circle beta) /\ ~(b on_circle beta) -> 
        IntersectsCC alpha beta.

(*
5. If a is on α, b is in α, a is in β, and b is on β, then α and β intersect.
*)
Axiom intersection_circle_circle_2: forall (a b : Point) (alpha beta : Circle), 
    (a on_circle alpha) /\ (b in_circle alpha) /\ (a in_circle beta) /\ (b on_circle beta) ->
        IntersectsCC alpha beta.

(* equality axioms *)

(*
1. 
x = x
*) 

(*
2. 
If x = y and ϕ(x), then ϕ(y)
*)
