(*
Metric inferences defined in Sec. 3.5 of Avigad et al. 2009
*)
Require Import Sorts.
Open Scope R.

(* + is associative and commutative, with identity 0. *)

(* < is a linear ordering with least element 0 *)

(* For any x, y, and z, if x < y then x + z < y + z *)

(*
1. 
ab = 0 if and only if a = b.
*)
Axiom zero_segment_if : forall (a b : Point), 
    segment2real (SegmentPP a b) = 0 -> a = b.

Axiom zero_segment_onlyif : forall (a b : Point), 
    a = b -> segment2real (SegmentPP a b) = 0.

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
    (SegmentPP a b  == SegmentPP b a)%segment.

(*
4. 
a != b and b != c imply \abc = \cba.
*)
Axiom angle_symm : forall (a b c : Point),
    (a <> b) /\ (b <> c) -> (AnglePPP a b c == AnglePPP c b a)%angle.

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
Axiom degenerated_area : forall (a b : Point), area2real (AreaPPP a a b) = 0.

(*
7. 
△abc ≥ 0.
*)
Axiom area_gte_zero : forall (ar : Area), 0 <= ar.

(*
8. 
△abc = △cab and △abc = △acb.
*)
Axiom area_symm_1 : forall (a b c : Point),
    (AreaPPP a b c == AreaPPP c a b)%area.

Axiom area_symm_2 : forall (a b c : Point),
    (AreaPPP a b c == AreaPPP a c b)%area.

(*
9. 
If ab = a′b′, bc = b′c′, ca = c′a′, \abc = \a′b′c′, \bca = \b′c′a′, and
\cab = \c′a′b′, then △abc = △a′b′c′.
*)
Axiom area_congruence : forall (a b c a' b' c' : Point),
    (SegmentPP a b == SegmentPP a' b')%segment /\ (SegmentPP b c == SegmentPP b' c')%segment /\ 
    (SegmentPP c a == SegmentPP c' a')%segment /\ (AnglePPP a b c == AnglePPP a' b' c')%angle /\ 
    (AnglePPP b c a == AnglePPP b' c' a')%angle /\ (AnglePPP c a b == AnglePPP c' a' b')%angle ->
        (AreaPPP a b c == AreaPPP a' b' c')%area.