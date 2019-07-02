Require Import Axioms.


Theorem proposition_1 : forall (a b : Point), a <> b ->
    exists c : Point, (Segment_PP c a == Segment_PP c b == Segment_PP a b)%segment.
Proof.  
    euclid_intros.
    euclid_apply (ConstructionRules.circle_from_points a b) as BCD. (* construct a circle centered around a *)
    euclid_apply (ConstructionRules.circle_from_points b a) as ACE. (* construct a circle centered around b *)
    euclid_apply (ConstructionRules.intersection_circles BCD ACE) as c.  (* construct the intersection c between two circles *)
    exists c.
    euclid_apply (TransferInferences.point_on_circle_onlyif a b c BCD).  (* deduce ac = ab *)
    euclid_apply (TransferInferences.point_on_circle_onlyif b a c ACE).  (* deduce bc = ba *) 
    (* metric inferences *)
    euclid_apply (MetricInferences.segment_symm a b).
    euclid_apply (MetricInferences.segment_symm a c). 
    euclid_apply (MetricInferences.segment_symm b c).
    lra. 
all: fail. Admitted.


Theorem proposition_2 : forall (a b c : Point), 
    a <> b /\  b <> c ->
    exists l : Point, (Segment_PP a l == Segment_PP b c)%segment.
Proof.
    euclid_intros.
    euclid_apply (proposition_1 a b) as d.
    euclid_apply (ConstructionRules.line_from_points d a) as AE.
    euclid_apply (ConstructionRules.line_from_points d b) as BF.
    euclid_apply (ConstructionRules.circle_from_points b c) as CGH.
    euclid_apply (ConstructionRules.intersection_circle_line_extending_points CGH BF b d) as g.
    euclid_apply (ConstructionRules.circle_from_points d g) as GKL.
    euclid_apply (ConstructionRules.intersection_circle_line_extending_points GKL AE a d) as l.
    euclid_apply (TransferInferences.point_on_circle_onlyif b c g CGH).
    euclid_apply (TransferInferences.point_on_circle_onlyif d l g GKL).
    euclid_apply (TransferInferences.between d a l).
    euclid_apply (TransferInferences.between d b g).
    exists l.
    lra.
all: fail. Admitted.


Theorem proposition_3 : forall (a b c0 c1 : Point), 
    a <> c0 /\ c0 <> c1 /\ (Segment_PP a b > Segment_PP c0 c1)  ->
    exists e : Point, (Between a e b) /\ (Segment_PP a e == Segment_PP c0 c1)%segment. 
Proof.
    euclid_intros.
    euclid_apply (proposition_2 a c0 c1) as d.
    euclid_apply (ConstructionRules.circle_from_points a d) as DEF.
    euclid_apply (ConstructionRules.line_from_points a b) as AB.
    euclid_apply (ConstructionRules.intersection_circle_line_between_points DEF AB a b) as e.
    euclid_apply (TransferInferences.point_on_circle_onlyif a d e).
    exists e.
    split.
    + assumption.
    + lra.
all: fail. Admitted.

Theorem proposition_4 : forall (a b c d e f : Point), 
    d <> e /\ e <> f /\ f <> d /\
     ~(Between b a c) /\ ~(Between a b c) /\ ~(Between a c b) /\ 
     ~(Between e d f) /\ ~(Between d e f) /\ ~(Between d f e) /\
    (Segment_PP a b == Segment_PP d e)%segment /\
    (Segment_PP a c == Segment_PP d f)%segment /\
    (Angle_PPP b a c == Angle_PPP e d f)%angle -> 
    (Segment_PP b c == Segment_PP e f)%segment /\
    (Angle_PPP a b c == Angle_PPP d e f)%angle /\
    (Angle_PPP a c b == Angle_PPP d f e)%angle.
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.line_from_points d e) as DE.
    (* diff *)
    euclid_superposition (SuperpositionInferences.SAS b a c e d f DE) as a' c'.
    euclid_trivial.
all: fail. Admitted.


(* add a hypothesis: AE > AD *)
(* theorem cannot be represented in canonical form *)
Theorem proposition_5 : forall (a b c d e : Point), 
    b <> c /\ ~(Between b a c) /\ (Segment_PP a b == Segment_PP a c)%segment /\
    (Between a b d) /\ (Between a c e) /\ (Segment_PP a e > Segment_PP a d) ->
    (Angle_PPP a b c == Angle_PPP a c b)%angle /\ (Angle_PPP c b d == Angle_PPP b c e)%angle.
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.line_from_points a d) as AD.
    euclid_apply (ConstructionRules.line_from_points a e) as AE.
    euclid_apply (ConstructionRules.point_between_points AD b d) as f.
    euclid_apply (proposition_3 a e f a) as g.
    euclid_apply (equal_angles a f f c g AD AE).
    euclid_apply (equal_angles a g g b f AE AD).
    euclid_apply (proposition_4 a f c a g b).
    euclid_apply (ConstructionRules.line_from_points c f) as CF.
    euclid_apply (ConstructionRules.line_from_points b g) as BG.
    euclid_apply (TransferInferences.equal_angles g a c b b AE BG).
    euclid_apply (proposition_4 f b c g c b).
    split.
    (* diff *)
    + euclid_apply (ConstructionRules.line_from_points b g) as BG.
        euclid_apply (ConstructionRules.line_from_points c f) as CF.
        euclid_apply (TransferInferences.sum_angles_onlyif b a g c AD BG).
        euclid_apply (TransferInferences.sum_angles_onlyif c a f b AE CF).
        euclid_apply (MetricInferences.angle_symm f c b).
        euclid_apply (MetricInferences.angle_symm g b c).
        lra.
    + euclid_apply (ConstructionRules.line_from_points b c) as BC. 
        euclid_apply (TransferInferences.equal_angles b d f c c AD BC).
        euclid_apply (MetricInferences.angle_symm c b d).
        euclid_apply (TransferInferences.equal_angles c g e b b AE BC).
        euclid_apply (MetricInferences.angle_symm b c e).
        lra.
all: fail. Admitted.




Theorem proposition_6 : forall (a b c : Point), 
    a <> b /\ a <> c /\ b <> c /\ ~(Between b a c) /\
    (Angle_PPP a b c == Angle_PPP a c b)%angle ->
    (Segment_PP a b == Segment_PP a c)%segment.
Proof.
    euclid_intros.
    euclid_contradict.
    euclid_case (Segment_PP a b > Segment_PP a c).
    + admit.
    + euclid_case (Segment_PP a b < Segment_PP a c). 
       - admit.
       - euclid_trivial. 
(*
unfold not in not_phi0.
euclid_apply (proposition_3 b a a c) as d.
       (* diff *)
       euclid_apply (ConstructionRules.line_from_points a b) as AB. 
       euclid_apply (ConstructionRules.line_from_points c b) as CB. 
       euclid_apply (TransferInferences.equal_angles b d a c c AB CB).
       euclid_apply (proposition_4 b d c c a b). 
       euclid_apply (sum_areas_if a b d c AB).
       euclid_apply (area_congruence b d c c a b).
       euclid_apply (degenerated_area_if a d c AB).*)
Admitted.
    


Theorem proposition_7 : forall (a b c d : Point) (AB : Line), 
    a on_line AB /\ b on_line AB /\ c <> d /\ (Segment_PP a c == Segment_PP a d)%segment /\ 
    (Segment_PP c b == Segment_PP d b)%segment /\ (SameSide c d AB) -> 
    False.
Proof. 
    euclid_intros.
Admitted.



Theorem proposition_8 : forall (a b c d e f : Point), 
    (Segment_PP a b == Segment_PP d e)%segment /\  (Segment_PP a c == Segment_PP d f)%segment /\
    (Segment_PP b c == Segment_PP e f)%segment ->
    (Angle_PPP b a c == Angle_PPP e d f)%angle.
Proof.
Admitted.
    


Theorem proposition_9 : forall (a b c : Point), 
    exists f : Point, (Angle_PPP b a f == Angle_PPP c a f)%angle.
Proof.
Admitted.


Theorem proposition_10 : forall (a b : Point), 
    exists d : Point, (Between a d b) /\ (Segment_PP a d == Segment_PP d b)%segment.
Proof.
Admitted.
