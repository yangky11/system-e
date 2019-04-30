(* Six sorts: point, line, circle, segment, angle, area *)
Require Export Reals.
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