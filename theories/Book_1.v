Require Import Axioms.

Lemma foo : True.
Proof.
    hello. 
    smt. 
    
    now auto.
Qed.


Theorem proposition_1 : forall (a b : Point), a <> b ->
    exists c : Point, (Segment_PP c a == Segment_PP c b == Segment_PP a b)%segment.
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.circle_from_points a b) as alpha. (* construct a circle centered around a *)
    euclid_apply (ConstructionRules.circle_from_points b a) as beta. (* construct a circle centered around b *)
    euclid_apply (ConstructionRules.intersection_circles alpha beta) as c.  (* construct the intersection c between two circles *)
    exists c.
    euclid_apply (TransferInferences.point_on_circle_onlyif a b c alpha).  (* deduce ac = ab *)
    euclid_apply (TransferInferences.point_on_circle_onlyif b a c beta).  (* deduce bc = ba *) 
    (* metric inferences *)
    euclid_apply (MetricInferences.segment_symm a c).
    euclid_apply (MetricInferences.segment_symm b c).
    euclid_apply (MetricInferences.segment_symm a b).
    lra. 
all: fail. Admitted.

(*
Theorem proposition_2 : forall (a b c : Point), a <> b /\ b <> c ->
    exists l : Point, (Segment_PP a l == Segment_PP b c)%segment.
Proof.
    euclid_intros.
    euclid_apply (proposition_1 a b) as d.
    euclid_apply (ConstructionRules.line_from_points d a) as AE.
    euclid_apply (ConstructionRules.line_from_points d b) as BF.
    euclid_apply (ConstructionRules.circle_from_points b c) as CGH.
    euclid_apply (ConstructionRules.intersection_circle_line CGH AE) as g.
    euclid_apply (ConstructionRules.circle_from_points d g) as GKL.
    euclid_apply (ConstructionRules.intersection_circle_line GKL BF) as l.
    euclid_apply (TransferInferences.point_on_circle_onlyif b c g CGH).
    euclid_apply (TransferInferences.point_on_circle_onlyif d l g GKL).
    euclid_apply (TransferInferences.between d a l).
    euclid_apply (TransferInferences.between d b g).
    exists l.
    lra.
all: fail. Admitted.



Theorem proposition_3 : forall (a b c0 c1 : Point), a <> c0 /\ c0 <> c1 /\ (Segment_PP a b > Segment_PP c0 c1)  ->
    exists e : Point, (Between a e b) /\ (Segment_PP a e == Segment_PP c0 c1)%segment. 
Proof. euclid_smt. 
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


Axiom SAS : forall (a b c d g h : Point) (L : Line), 
    ~(Between b a c) /\ ~(Between a b c) /\ (Between a c b) /\
    d on_line L /\ g on_line L /\ ~(h on_line L) -> 
    exists (b' c' : Point), (Angle_PPP d b' c' == Angle_PPP a b c)%angle /\ 
        b' on_line L /\ ~(Between b' d g) /\ (SameSide c' h L) /\ 
        (Segment_PP d b' == Segment_PP a b)%segment /\
        (Segment_PP b' c' == Segment_PP b c)%segment /\
        (Segment_PP c' d == Segment_PP c a)%segment.

Axiom proposition_4 : forall (a b c d e f : Point), 
    a <> b /\ a <> c /\ 
    (Segment_PP a b == Segment_PP d e)%segment /\
    (Segment_PP a c == Segment_PP d f)%segment /\
    (Angle_PPP b a c == Angle_PPP e d f)%angle -> 
    (Segment_PP b c == Segment_PP e f)%segment /\
    (Angle_PPP a b c == Angle_PPP d e f)%angle /\
    (Angle_PPP a c b == Angle_PPP d f e)%angle.

(* add a hypothesis: AE > AD *)
Theorem proposition_5 : forall (a b c d e: Point), 
    (Segment_PP a b == Segment_PP a c)%segment /\ (Between a b d) /\ (Between a c e) /\ (Segment_PP a e > Segment_PP a d) ->
    (Angle_PPP a b c == Angle_PPP a c b)%angle /\ (Angle_PPP c b d == Angle_PPP b c e)%angle.
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.line_from_points a d) as AD.
    euclid_apply (ConstructionRules.line_from_points a e) as AE.
    euclid_apply (ConstructionRules.point_between_points AD b d) as f.
    euclid_apply (proposition_3 a e f a) as g.
    euclid_apply (proposition_4 a f c a g b).
    euclid_apply (proposition_4 f b c g c b).
    split.
    (* somewhat different from the book *)
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

Goal forall (a b c : Point), (Segment_PP a b == Segment_PP a c)%segment.
Proof.
    euclid_smt.
all: fail. Admitted.

Theorem proposition_6 : forall (a b c : Point), 
    (Angle_PPP a b c == Angle_PPP a c b)%angle ->
    (Segment_PP a b == Segment_PP a c)%segment.
Proof.
    (* many theorems are provable by euclid_smt *)
 all: fail. Admitted.

*)