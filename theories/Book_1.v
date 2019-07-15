Add ML Path "/Users/yangky/.opam/4.07.1+flambda/lib/z3".
Require Import SystemE.Axioms.


Theorem proposition_1 : forall (a b : Point), a <> b ->
    exists c : Point, (Segment_PP c a == Segment_PP c b == Segment_PP a b)%segment.
Proof.  
    euclid_intros.
    euclid_apply (ConstructionRules.circle_from_points a b) as BCD.
    euclid_apply (ConstructionRules.circle_from_points b a) as ACE.
    euclid_apply (ConstructionRules.intersection_circles BCD ACE) as c. 
    euclid_apply (TransferInferences.point_on_circle_onlyif a b c BCD).
    euclid_apply (TransferInferences.point_on_circle_onlyif b a c ACE). 
    exists c.
    euclid_trivial.
all: fail. Admitted.


(* a generalized version of proposition_1 that is required by later theorems *)
Theorem proposition_1' : forall (a b d : Point) (AB : Line), 
    a <> b /\ a on_line AB /\ b on_line AB /\ ~(d on_line AB) ->
    exists c : Point, 
    (Segment_PP c a == Segment_PP c b == Segment_PP a b)%segment /\ ~(SameSide c d AB).
Proof.  
    euclid_intros.
    euclid_apply (ConstructionRules.circle_from_points a b) as BCD.
    euclid_apply (ConstructionRules.circle_from_points b a) as ACE.
    euclid_apply (ConstructionRules.intersection_opposite_side BCD ACE d a b AB) as c.
    euclid_apply (TransferInferences.point_on_circle_onlyif a b c BCD).
    euclid_apply (TransferInferences.point_on_circle_onlyif b a c ACE). 
    exists c.
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_2 : forall (a b c : Point), b <> c ->
    exists l : Point, (Segment_PP a l == Segment_PP b c)%segment.
Proof.
    euclid_intros.
    euclid_case (a = b).
    + exists c.
        euclid_trivial.
    + euclid_apply (proposition_1 a b) as d.
        euclid_apply (ConstructionRules.line_from_points d a) as AE.
        euclid_apply (ConstructionRules.line_from_points d b) as BF.
        euclid_apply (ConstructionRules.circle_from_points b c) as CGH.
        euclid_apply (ConstructionRules.intersection_circle_line_extending_points CGH BF b d) as g.
        euclid_apply (ConstructionRules.circle_from_points d g) as GKL.
        euclid_apply (ConstructionRules.intersection_circle_line_extending_points GKL AE a d) as l.
        euclid_apply (TransferInferences.point_on_circle_onlyif b c g CGH).
        euclid_apply (TransferInferences.point_on_circle_onlyif d l g GKL).
        euclid_apply (TransferInferences.between_if d a l).
        euclid_apply (TransferInferences.between_if d b g).
        exists l.
        euclid_trivial.
all: fail. Admitted.


Theorem proposition_3 : forall (a b c0 c1 : Point), 
    a <> b /\ c0 <> c1 /\ (Segment_PP a b > Segment_PP c0 c1)  ->
    exists e : Point, (Between a e b) /\ (Segment_PP a e == Segment_PP c0 c1)%segment. 
Proof.
    euclid_intros.
    euclid_apply (proposition_2 a c0 c1) as d.
    euclid_apply (ConstructionRules.circle_from_points a d) as DEF.
    euclid_apply (ConstructionRules.line_from_points a b) as AB.
    euclid_apply (ConstructionRules.intersection_circle_line_between_points DEF AB a b) as e.
    euclid_apply (TransferInferences.point_on_circle_onlyif a d e).
    exists e.
    euclid_trivial.
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
    euclid_apply (SuperpositionInferences.SAS a b c d e f DE) as b' c'.
    euclid_trivial (b' = e).
    euclid_trivial (c' = f).
    euclid_trivial.
all: fail. Admitted.


(* theorem cannot be represented in canonical form *)
Theorem proposition_5 : forall (a b c d e : Point), 
    b <> c /\ ~(Between b a c) /\ (Segment_PP a b == Segment_PP a c)%segment /\
    (Between a b d) /\ (Between a c e) ->
    (Angle_PPP a b c == Angle_PPP a c b)%angle /\ (Angle_PPP c b d == Angle_PPP b c e)%angle.
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.line_from_points a d) as AD.
    euclid_apply (ConstructionRules.line_from_points a e) as AE.
    euclid_apply (ConstructionRules.point_between_points_shorter_than AD b d c e) as f.
    euclid_apply (proposition_3 a e f a) as g.
    euclid_apply (ConstructionRules.line_from_points c f) as CF.
    euclid_apply (ConstructionRules.line_from_points b g) as BG.
    euclid_apply (proposition_4 a f c a g b).
    euclid_trivial (Segment_PP b f == Segment_PP c g)%segment.
    euclid_apply (proposition_4 f b c g c b).
    split.
    + euclid_apply (TransferInferences.sum_angles_onlyif b a g c AD BG).
        euclid_apply (TransferInferences.sum_angles_onlyif c a f b AE CF).
        euclid_trivial.
    + euclid_apply (ConstructionRules.line_from_points b c) as BC. 
        euclid_trivial.
all: fail. Admitted.


Theorem proposition_6 : forall (a b c : Point), 
    a <> b /\ a <> c /\ b <> c /\ ~(Between b a c) /\
    (Angle_PPP a b c == Angle_PPP a c b)%angle ->
    (Segment_PP a b == Segment_PP a c)%segment.
Proof.
    euclid_intros.
    euclid_contradict.
    euclid_case (Segment_PP a b > Segment_PP a c).
    + euclid_apply (proposition_3 b a a c) as d.
        euclid_apply (ConstructionRules.line_from_points a b) as AB. 
        euclid_apply (ConstructionRules.line_from_points b c) as BC. 
        euclid_apply (proposition_4 b d c c a b).
        euclid_trivial.
    + euclid_case (Segment_PP a b < Segment_PP a c). 
       - euclid_apply (proposition_3 c a a b) as d.
          euclid_apply (ConstructionRules.line_from_points a c) as AC. 
          euclid_apply (ConstructionRules.line_from_points c b) as CB. 
          euclid_apply (proposition_4 c d b b a c).
          euclid_trivial.
       - euclid_trivial. 
all:fail. Admitted.



Theorem proposition_7 : forall (a b c d : Point) (AB : Line), 
    a on_line AB /\ b on_line AB /\ (SameSide c d AB) /\ a <> b /\  c <> d /\
    (Segment_PP a c == Segment_PP a d)%segment /\ (Segment_PP c b == Segment_PP d b)%segment -> 
    False.
Proof. 
    euclid_intros.
    euclid_apply (ConstructionRules.line_from_points a c) as AC.
    euclid_apply (ConstructionRules.extend_point AC a c) as e.
    euclid_apply (ConstructionRules.line_from_points a d) as AD.
    euclid_apply (ConstructionRules.extend_point AD a d) as f.
    euclid_apply (proposition_5 a c d e f).
    euclid_apply (ConstructionRules.line_from_points b c) as BC.
    euclid_apply (ConstructionRules.extend_point BC b c) as g.
    euclid_apply (ConstructionRules.line_from_points b d) as BD.
    euclid_apply (ConstructionRules.extend_point BD b d) as h.
    euclid_apply (proposition_5 b c d g h).
    euclid_apply (ConstructionRules.line_from_points c d) as CD.
    euclid_case (SameSide a b CD).
    + euclid_case (SameSide d b AC).
        - euclid_apply (TransferInferences.sum_angles_onlyif c a d b AC CD).
            euclid_apply (TransferInferences.sum_angles_onlyif d c b a CD BD).
            euclid_trivial.
        - euclid_trivial.
    + euclid_case (SameSide d b AC). 
        - euclid_trivial.
        - euclid_trivial.
all: fail. Admitted.


Theorem proposition_8 : forall (a b c d e f : Point), 
     ~(Between a b c) /\ ~(Between b c a) /\ ~(Between c a b) /\
    d <> e /\ e <> f /\ f <> d /\ ~(Between d e f) /\ ~(Between e f d) /\ ~(Between f d e) /\
    (Segment_PP a b == Segment_PP d e)%segment /\  (Segment_PP a c == Segment_PP d f)%segment /\
    (Segment_PP b c == Segment_PP e f)%segment ->
    (Angle_PPP b a c == Angle_PPP e d f)%angle.
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.line_from_points e f) as EF.
    euclid_apply (SuperpositionInferences.SAS b c a e f d EF) as c' a'.
    euclid_trivial (c' = f).
    euclid_case (a' = d).
    + euclid_trivial.
    + euclid_apply (ConstructionRules.line_from_points d a') as DA'.
        euclid_apply (ConstructionRules.line_from_points d e) as DE.
        euclid_apply (proposition_7 e f d a' EF).
        contradiction.
all: fail. Admitted.


Theorem proposition_9 : forall (a b c : Point), 
    a <> b /\ b <> c /\ c <> a /\ ~(Between a b c) /\ ~(Between b c a) /\ ~(Between c a b) ->
    exists f : Point, f <> a /\ (Angle_PPP b a f == Angle_PPP c a f)%angle.
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.line_from_points a b) as AB.
    euclid_apply (ConstructionRules.line_from_points a c) as AC.
    euclid_apply (ConstructionRules.point_between_points_shorter_than AB a b a c) as d.
    euclid_apply (proposition_3 a c a d) as e.
    euclid_apply (ConstructionRules.line_from_points d e) as DE.
    euclid_apply (proposition_1' d e a DE) as f. 
    euclid_apply (proposition_8 a d f a e f).
    exists f. 
    euclid_apply (ConstructionRules.line_from_points a f) as AF.
    split.
    + assumption.
    + euclid_trivial.
all:fail. Admitted.


Theorem proposition_10 : forall (a b : Point), a <> b ->
    exists d : Point, (Between a d b) /\ (Segment_PP a d == Segment_PP d b)%segment.
Proof.
    euclid_intros.
    euclid_apply (proposition_1 a b) as c.
    euclid_apply (proposition_9 c a b) as d'.
    euclid_apply (ConstructionRules.line_from_points c d') as CD'.
     euclid_apply (ConstructionRules.line_from_points a b) as AB.
    euclid_apply (ConstructionRules.intersection_lines CD' AB) as d.
    exists d.
    euclid_apply (proposition_4 c a d c b d).
    euclid_trivial.
all:fail. Admitted.


Theorem proposition_11 : forall (a b c : Point) (AB : Line), 
    Between a c b /\ a on_line AB /\ b on_line AB ->
    exists f : Point, ~(f on_line AB) /\ (Angle_PPP a c f == RightAngle)%angle.
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.point_between_points_shorter_than AB c a c b) as d.
    euclid_apply (proposition_3 c b c d) as e.
    euclid_apply (proposition_1 d e) as f.
    exists f.
    euclid_apply (proposition_8 c d f c e f).
    euclid_apply (TransferInferences.perpendicular_if d e c f AB).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_11' : forall (a b c g : Point) (AB : Line), 
    Between a c b /\ a on_line AB /\ b on_line AB /\ ~(g on_line AB) ->
    exists f : Point, (SameSide f g AB) /\ (Angle_PPP a c f == RightAngle)%angle.
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.point_between_points_shorter_than AB c a c b) as d.
    euclid_apply (proposition_3 c b c d) as e.
    euclid_apply (ConstructionRules.point_opposite_side AB g) as h.
    euclid_apply (proposition_1' d e h AB) as f.
    exists f.
    euclid_apply (proposition_8 c d f c e f).
    euclid_apply (TransferInferences.perpendicular_if d e c f AB).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_12 : forall (L : Line) (a c : Point), 
    a on_line L /\ ~ (c on_line L) ->
    exists h : Point, h on_line L /\ (Angle_PPP a h c == RightAngle)%angle.
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.point_opposite_side L c) as d.
    euclid_apply (ConstructionRules.circle_from_points c d) as EFG.
    euclid_apply (ConstructionRules.intersections_circle_line EFG L) as e g.
    euclid_apply (proposition_10 e g) as h.
    euclid_apply (ConstructionRules.line_from_points c h) as CH.
    exists h.
    euclid_apply (proposition_8 h c g h c e).
    euclid_apply (TransferInferences.perpendicular_if g e h c L).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_13 : forall (DC BA : Line) (a b c d : Point), 
    b on_line DC /\ b on_line BA /\ d on_line DC /\ c on_line DC /\ (Between d b c) /\ a on_line BA /\ a <> b /\ DC <> BA ->
    (angle2real (Angle_PPP c b a)) + (angle2real (Angle_PPP a b d)) = (angle2real RightAngle) + (angle2real RightAngle).
Proof.
    euclid_intros.
    euclid_case (Angle_PPP c b a == Angle_PPP a b d)%angle.
    + euclid_trivial.
    + euclid_apply (proposition_11' d c b a DC) as e. 
        euclid_apply (ConstructionRules.line_from_points b e) as BE.
        euclid_case (SameSide c a BE).
        - euclid_apply (TransferInferences.sum_angles_onlyif b c e a DC BE).
           euclid_trivial.
        - euclid_apply (TransferInferences.sum_angles_onlyif b d e a DC BE).
           euclid_trivial.
all: fail. Admitted.


Theorem proposition_14 : forall (BC BD : Line) (a b c d : Point), 
    b on_line BC /\ b on_line BD /\ c on_line BC /\ d on_line BD /\ ~(a on_line BC) /\ 
    ~(a on_line BD) /\ a <> b /\ b <> c /\ b <> d /\ (d on_line BC \/ SameSide a d BC) /\ (c on_line BD \/ SameSide a c BD) /\
    (angle2real (Angle_PPP a b c)) + (angle2real (Angle_PPP a b d)) = (angle2real RightAngle) + (angle2real RightAngle) ->
    BC = BD.
Proof.
    euclid_intros.
    euclid_contradict.
    euclid_apply (ConstructionRules.extend_point BC c b) as e.
    euclid_apply (ConstructionRules.line_from_points a b) as AB.
    euclid_apply (proposition_13 BC AB a b e c). 
    euclid_trivial.
Admitted.


Theorem proposition_15 : forall (a b c d e : Point) (AB CD : Line), 
    a on_line AB /\ b on_line AB /\ c on_line CD /\ d on_line CD /\ e on_line AB /\ e on_line CD /\ 
    CD <> AB /\ (Between d e c) /\ (Between a e b) ->
    (Angle_PPP a e c == Angle_PPP d e b)%angle /\ (Angle_PPP c e b == Angle_PPP a e d)%angle.
Proof.
    euclid_intros.
    euclid_apply (proposition_13 CD AB a e c d). 
    euclid_apply (proposition_13 AB CD d e a b).
    euclid_apply (proposition_13 AB CD c e a b).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_16 : forall (a b c d : Point) (BC : Line), 
    (Between b c d) /\ b on_line BC /\ c on_line BC /\ ~(a on_line BC) ->
    (Angle_PPP a c d > Angle_PPP c b a) /\ (Angle_PPP a c d > Angle_PPP b a c).
Proof.
    euclid_intros.
    split.
    + euclid_apply (proposition_10 b c) as e.
        euclid_apply (ConstructionRules.line_from_points a e) as AE.
        euclid_apply (ConstructionRules.extend_point_longer AE a e (Segment_PP a e)) as f'.
        euclid_apply (proposition_3 e f' a e) as f.
        euclid_apply (proposition_15 b c a f e BC AE).
        euclid_apply (proposition_4 e b a e c f).
        euclid_apply (ConstructionRules.line_from_points a c) as AC.
        euclid_apply (ConstructionRules.extend_point AC a c) as g.
        euclid_apply (TransferInferences.sum_angles_onlyif c b g f BC AC).
        euclid_apply (proposition_15 a g b d c AC BC). 
        euclid_apply (ConstructionRules.line_from_points a b) as AB.
        euclid_trivial.
    + euclid_apply (proposition_10 a c) as e.
        euclid_apply (ConstructionRules.line_from_points b e) as BE.
        euclid_apply (ConstructionRules.extend_point_longer BE b e (Segment_PP b e)) as f'.
        euclid_apply (proposition_3 e f' b e) as f.
        euclid_apply (ConstructionRules.line_from_points a c) as AC.
        euclid_apply (proposition_15 a c b f e AC BE).
        euclid_apply (proposition_4 e a b e c f).
        euclid_apply (TransferInferences.sum_angles_onlyif c a d f AC BC).
        euclid_apply (ConstructionRules.line_from_points a b) as AB.
        euclid_trivial.
all: fail. Admitted.


Theorem proposition_17 : forall (a b c : Point) (BC : Line), 
    b <> c /\ b on_line BC /\ c on_line BC /\ ~(a on_line BC) ->
    (angle2real (Angle_PPP a b c)) + (angle2real (Angle_PPP b c a))  < (angle2real RightAngle) + (angle2real RightAngle).
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.extend_point BC b c) as d.
    euclid_apply (proposition_16 a b c d BC).
    euclid_apply (ConstructionRules.line_from_points a c) as AC.
    euclid_apply (proposition_13 BC AC a c b d).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_18 : forall (a b c : Point) (AC : Line),
    a <> b /\ a on_line AC /\ c on_line AC /\ ~(b on_line AC) /\ 
    (Segment_PP a c > Segment_PP a b) -> 
    (Angle_PPP a b c > Angle_PPP b c a).
Proof.
    euclid_intros.
    euclid_apply (proposition_3 a c a b) as d.
    euclid_apply (proposition_16 b c d a AC). 
    euclid_apply (ConstructionRules.line_from_points a b) as AB.
    euclid_apply (ConstructionRules.extend_point AB a b) as e.
    euclid_apply (proposition_5 a b d e c).
    euclid_apply (ConstructionRules.line_from_points b c) as BC.
    euclid_apply (TransferInferences.sum_angles_if b a c d AB BC).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_19 : forall (a b c : Point), 
    a <> c /\ b <> c /\ (Angle_PPP a b c > Angle_PPP b c a) -> 
    (Segment_PP a c > Segment_PP a b).
Proof.
    euclid_intros.
    euclid_contradict.
    euclid_apply (ConstructionRules.line_from_points a b) as AB.
    euclid_apply (ConstructionRules.line_from_points a c) as AC.
    euclid_case (Segment_PP a c == Segment_PP a b)%segment.
    +  euclid_apply (ConstructionRules.extend_point AB a b) as d.
        euclid_apply (ConstructionRules.extend_point AC a c) as e.
        euclid_apply (proposition_5 a b c d e).
        euclid_trivial.
    + euclid_apply (proposition_18 a c b AB).
        euclid_trivial.
all:fail. Admitted.


Theorem proposition_20 : forall (a b c : Point) (BC : Line),
    b <> c /\ b on_line BC /\ c on_line BC /\ ~(a on_line BC) -> 
    (Segment_PP b a + Segment_PP a c > Segment_PP b c).
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.line_from_points b a) as BA.
    euclid_apply (ConstructionRules.extend_point_longer BA b a (Segment_PP c a)) as d'.
    euclid_apply (proposition_3 a d' a c) as d.
    euclid_apply (ConstructionRules.line_from_points a c) as AC.
    euclid_apply (ConstructionRules.extend_point AC a c) as c'.
    euclid_apply (proposition_5 a c d c' d').
    euclid_apply (ConstructionRules.line_from_points c d) as CD.
    euclid_apply (TransferInferences.sum_angles_onlyif c b d a BC CD).
    euclid_trivial (Angle_PPP b c d > Angle_PPP a d c).
    euclid_apply (proposition_19 b c d).
    euclid_trivial.
all:fail. Admitted.