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