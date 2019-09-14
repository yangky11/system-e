Add ML Path "/Users/yangky/.opam/4.07.1+flambda/lib/z3".
Require Import SystemE.Axioms.


Theorem proposition_1 : forall (a b : Point) (AB : Line), DistinctPointsOnL a b AB ->
    exists c : Point, (SegmentPP c a == SegmentPP a b)%segment /\ (SegmentPP c b == SegmentPP a b)%segment.
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


Theorem proposition_1' : forall (a b f : Point) (AB : Line), 
    DistinctPointsOnL a b AB /\ ~(f on_line AB) ->
    exists c : Point, 
    (SegmentPP c a == SegmentPP a b)%segment /\ (SegmentPP c b == SegmentPP a b)%segment /\ (OppositeSide c f AB).
Proof.  
    euclid_intros.
    euclid_apply (ConstructionRules.circle_from_points a b) as BCD.
    euclid_apply (ConstructionRules.circle_from_points b a) as ACE.
    euclid_apply (ConstructionRules.intersection_opposite_side BCD ACE f a b AB) as c.
    euclid_apply (TransferInferences.point_on_circle_onlyif a b c BCD).
    euclid_apply (TransferInferences.point_on_circle_onlyif b a c ACE). 
    exists c.
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_2 : forall (a b c : Point) (BC : Line), 
    DistinctPointsOnL b c BC /\ a <> b ->
    exists l : Point, (SegmentPP a l == SegmentPP b c)%segment.
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.line_from_points a b) as AB.
    euclid_apply (proposition_1 a b AB) as d.
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


Theorem proposition_2' : forall (a b c : Point) (BC : Line), DistinctPointsOnL b c BC ->
    exists l : Point, (SegmentPP a l == SegmentPP b c)%segment.
Proof.
    euclid_intros.
    euclid_case (a = b).
    + exists c.
        euclid_trivial.
    + euclid_apply (proposition_2 a b c BC) as l.
       exists l.
       assumption.
all: fail. Admitted.


Theorem proposition_3 : forall (a b c0 c1 : Point) (AB C : Line), 
    DistinctPointsOnL a b AB /\ DistinctPointsOnL c0 c1 C /\ a <> c0 /\ (SegmentPP a b > SegmentPP c0 c1)  ->
    exists e : Point, (Between a e b) /\ (SegmentPP a e == SegmentPP c0 c1)%segment. 
Proof.
    euclid_intros.
    euclid_apply (proposition_2 a c0 c1) as d.
    euclid_apply (ConstructionRules.circle_from_points a d) as DEF.
    euclid_apply (ConstructionRules.intersection_circle_line_between_points DEF AB a b) as e.
    euclid_apply (TransferInferences.point_on_circle_onlyif a d e).
    exists e.
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_3' : forall (a b c0 c1 : Point) (AB C : Line), 
    DistinctPointsOnL a b AB /\ DistinctPointsOnL c0 c1 C /\ (SegmentPP a b > SegmentPP c0 c1)  ->
    exists e : Point, (Between a e b) /\ (SegmentPP a e == SegmentPP c0 c1)%segment. 
Proof.
    euclid_intros.
    euclid_apply (proposition_2' a c0 c1) as d.
    euclid_apply (ConstructionRules.circle_from_points a d) as DEF.
    euclid_apply (ConstructionRules.intersection_circle_line_between_points DEF AB a b) as e.
    euclid_apply (TransferInferences.point_on_circle_onlyif a d e).
    exists e.
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_4 : forall (a b c d e f : Point) (AB BC AC DE EF DF : Line),
    Triangle a b c AB BC AC /\ Triangle d e f DE EF DF /\
    (SegmentPP a b == SegmentPP d e)%segment /\
    (SegmentPP a c == SegmentPP d f)%segment /\
    (AnglePPP b a c == AnglePPP e d f)%angle -> 
    (SegmentPP b c == SegmentPP e f)%segment /\
    (AnglePPP a b c == AnglePPP d e f)%angle /\
    (AnglePPP a c b == AnglePPP d f e)%angle.
Proof.
Admitted.


Theorem proposition_5 : forall (a b c d e : Point) (AB BC AC : Line), 
    Triangle a b c AB BC AC /\ (SegmentPP a b == SegmentPP a c)%segment /\
    (Between a b d) /\ (Between a c e) ->
    (AnglePPP a b c == AnglePPP a c b)%angle /\ (AnglePPP c b d == AnglePPP b c e)%angle.
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.point_between_points_shorter_than AB b d (SegmentPP c e)) as f.
    euclid_apply (proposition_3 a e f a AC AB) as g.
    euclid_apply (ConstructionRules.line_from_points c f) as FC.
    euclid_apply (ConstructionRules.line_from_points b g) as GB.
    euclid_apply (proposition_4 a f c a g b AB FC AC AC GB AB).
    euclid_trivial (SegmentPP b f == SegmentPP c g)%segment.
    euclid_apply (proposition_4 f b c g c b AB BC FC AC BC GB).
    euclid_apply (TransferInferences.sum_angles_onlyif b a g c AB GB).
    euclid_apply (TransferInferences.sum_angles_onlyif c a f b AC FC).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_5' : forall (a b c : Point) (AB BC AC : Line), 
    Triangle a b c AB BC AC /\ (SegmentPP a b == SegmentPP a c)%segment ->
    (AnglePPP a b c == AnglePPP a c b)%angle.
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.extend_point AB a b) as d.
    euclid_apply (ConstructionRules.extend_point AC a c) as e.
    euclid_apply (proposition_5 a b c d e AB BC AC).
    assumption.
all: fail. Admitted.


Theorem proposition_6 : forall (a b c : Point) (AB BC AC : Line), 
    Triangle a b c AB BC AC /\ (AnglePPP a b c == AnglePPP a c b)%angle ->
    (SegmentPP a b == SegmentPP a c)%segment.
Proof.
    euclid_intros.
    euclid_contradict.
    euclid_case (SegmentPP a b > SegmentPP a c).
    +  euclid_apply (proposition_3 b a a c AB AC) as d.
        euclid_apply (ConstructionRules.line_from_points d c) as DC.
        euclid_apply (proposition_4 b d c c a b AB DC BC AC AB BC).
        euclid_trivial.
    + euclid_apply (proposition_3 c a a b AC AB) as d.
        euclid_apply (ConstructionRules.line_from_points d b) as DB.
        euclid_apply (proposition_4 c d b b a c AC DB BC AB AC BC).
        euclid_trivial.
all:fail. Admitted.


Theorem proposition_7 : forall (a b c d : Point) (AB AC CB AD DB CD : Line), 
    DistinctPointsOnL a b AB /\ DistinctPointsOnL a c AC /\ DistinctPointsOnL c b CB /\
    DistinctPointsOnL a d AD /\ DistinctPointsOnL d b DB /\ (SameSide c d AB) /\  DistinctPointsOnL c d CD /\
    SameSide a b CD /\ SameSide d b AC /\ 
    (SegmentPP a c == SegmentPP a d)%segment /\ (SegmentPP c b == SegmentPP d b)%segment -> 
    False.
Proof. 
    euclid_intros.
    euclid_apply (proposition_5' a c d AC CD AD).
    euclid_apply (proposition_5' b c d CB CD DB).
    euclid_apply (TransferInferences.sum_angles_onlyif c a d b AC CD).
    euclid_apply (TransferInferences.sum_angles_onlyif d c b a CD DB).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_7' : forall (a b c d : Point) (AB AC CB AD DB : Line), 
    DistinctPointsOnL a b AB /\ DistinctPointsOnL a c AC /\ DistinctPointsOnL c b CB /\
    DistinctPointsOnL a d AD /\ DistinctPointsOnL d b DB /\ (SameSide c d AB) /\  c <> d /\
    (SegmentPP a c == SegmentPP a d)%segment /\ (SegmentPP c b == SegmentPP d b)%segment -> 
    False.
Proof. 
    euclid_intros.
    euclid_apply (ConstructionRules.extend_point AC a c) as e.
    euclid_apply (ConstructionRules.extend_point AD a d) as f.
    euclid_apply (ConstructionRules.line_from_points c d) as CD.
    euclid_apply (proposition_5 a c d e f AC CD AD).
    euclid_apply (ConstructionRules.extend_point CB b c) as g.
    euclid_apply (ConstructionRules.extend_point DB b d) as h.
    euclid_apply (proposition_5 b c d g h CB CD DB).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_8 : forall (a b c d e f : Point) (AB BC AC DE EF DF : Line), 
    Triangle a b c AB BC AC /\ Triangle d e f DE EF DF /\
    (SegmentPP a b == SegmentPP d e)%segment /\  (SegmentPP a c == SegmentPP d f)%segment /\
    (SegmentPP b c == SegmentPP e f)%segment ->
    (AnglePPP b a c == AnglePPP e d f)%angle.
Proof.
Admitted.


Theorem proposition_9 : forall (a b c : Point) (AB AC : Line),
    RectilinearAngle b a c AB AC /\ AB <> AC ->
    exists f : Point, f <> a /\ (AnglePPP b a f == AnglePPP c a f)%angle.
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.point_between_points_shorter_than AB a b (SegmentPP a c)) as d.
    euclid_apply (proposition_3' a c a d AC AB) as e.
    euclid_apply (ConstructionRules.line_from_points d e) as DE.
    euclid_apply (proposition_1' d e a DE) as f. 
    euclid_apply (ConstructionRules.line_from_points f e) as FE.
    euclid_apply (ConstructionRules.line_from_points f d) as FD.
    euclid_apply (ConstructionRules.line_from_points a f) as AF.
    exists f. 
    euclid_case (SameSide d e AF).
    + euclid_apply (proposition_7' a f d e AF AB FD AC FE).
       contradiction.
    + (* thanks to Proclus *)
       euclid_case (f on_line AB).
          euclid_apply (proposition_5' f d e AB DE FE).
          euclid_trivial (AnglePPP d e c > AnglePPP e d f).
          euclid_apply (proposition_5 a d e f c AB DE AC).
          euclid_trivial.
       - euclid_case (f on_line AC).
          * euclid_apply (proposition_5' f e d AC DE FD).
            euclid_trivial (AnglePPP e d b > AnglePPP d e f).
            euclid_apply (proposition_5 a d e b f AB DE AC).
            euclid_trivial.
          * euclid_apply (proposition_8 a d f a e f AB FD AF AC FE AF).
            euclid_trivial.
all:fail. Admitted.


Theorem proposition_9' : forall (a b c : Point) (AB AC : Line),
    RectilinearAngle b a c AB AC /\ AB <> AC  ->
    exists f : Point, (SameSide f c AB) /\ (SameSide f b AC) /\ (AnglePPP b a f == AnglePPP c a f)%angle.
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.point_between_points_shorter_than AB a b (SegmentPP a c)) as d.
    euclid_apply (proposition_3' a c a d AC AB) as e.
    euclid_apply (ConstructionRules.line_from_points d e) as DE.
    euclid_apply (proposition_1' d e a DE) as f. 
    euclid_apply (ConstructionRules.line_from_points f e) as FE.
    euclid_apply (ConstructionRules.line_from_points f d) as FD.
    euclid_apply (ConstructionRules.line_from_points a f) as AF.
    exists f. 
    euclid_case (SameSide d e AF).
    + euclid_apply (proposition_7' a f d e AF AB FD AC FE).
       contradiction.
    + (* thanks to Proclus *)
       euclid_case (f on_line AB).
       - euclid_apply (proposition_5' f d e AB DE FE).
          euclid_trivial (AnglePPP d e c > AnglePPP e d f).
          euclid_apply (proposition_5 a d e f c AB DE AC).
          euclid_trivial.
       - euclid_case (f on_line AC).
          * euclid_apply (proposition_5' f e d AC DE FD).
            euclid_trivial (AnglePPP e d b > AnglePPP d e f).
            euclid_apply (proposition_5 a d e b f AB DE AC).
            euclid_trivial.
          * euclid_apply (proposition_8 a d f a e f AB FD AF AC FE AF).
            euclid_apply (ConstructionRules.intersection_lines AF DE) as g. 
            euclid_trivial.
all:fail. Admitted.


Theorem proposition_10 : forall (a b : Point) (AB : Line), DistinctPointsOnL a b AB ->
    exists d : Point, (Between a d b) /\ (SegmentPP a d == SegmentPP d b)%segment.
Proof.
    euclid_intros.
    euclid_apply (proposition_1 a b) as c.
    euclid_apply (ConstructionRules.line_from_points c a) as AC.
    euclid_apply (ConstructionRules.line_from_points c b) as BC.
    euclid_apply (proposition_9' c a b AC BC) as d'.
    euclid_apply (ConstructionRules.line_from_points c d') as CD.
    euclid_apply (ConstructionRules.intersection_lines CD AB) as d.
    euclid_apply (proposition_4 c a d c b d AC AB CD BC AB CD).
    exists d.
    euclid_trivial.
all:fail. Admitted.


Theorem proposition_11 : forall (a b c : Point) (AB : Line), 
    DistinctPointsOnL a b AB /\ Between a c b ->
    exists f : Point, ~(f on_line AB) /\ (AnglePPP a c f == RightAngle)%angle.
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.point_between_points_shorter_than AB c a (SegmentPP c b)) as d.
    euclid_apply (proposition_3' c b c d) as e.
    euclid_apply (proposition_1 d e AB) as f.
    euclid_apply (ConstructionRules.line_from_points d f) as DF.
    euclid_apply (ConstructionRules.line_from_points f e) as FE.
    euclid_apply (ConstructionRules.line_from_points f c) as FC.
    euclid_apply (proposition_8 c d f c e f AB DF FC AB FE FC).
    euclid_apply (TransferInferences.perpendicular_if d e c f AB).
    exists f.
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_11' : forall (a b c g : Point) (AB : Line), 
    DistinctPointsOnL a b AB /\ Between a c b /\ ~(g on_line AB) ->
    exists f : Point, (SameSide f g AB) /\ (AnglePPP a c f == RightAngle)%angle.
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.point_between_points_shorter_than AB c a (SegmentPP c b)) as d.
    euclid_apply (proposition_3' c b c d) as e.
    euclid_apply (ConstructionRules.point_opposite_side AB g) as h.
    euclid_apply (proposition_1' d e h AB) as f.
    euclid_apply (ConstructionRules.line_from_points d f) as DF.
    euclid_apply (ConstructionRules.line_from_points f e) as FE.
    euclid_apply (ConstructionRules.line_from_points f c) as FC.
    euclid_apply (proposition_8 c d f c e f AB DF FC AB FE FC).
    euclid_apply (TransferInferences.perpendicular_if d e c f AB).
    exists f.
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_11'' : forall (a b : Point) (AB : Line), 
    DistinctPointsOnL a b AB ->
    exists f : Point, ~(f on_line AB) /\ (AnglePPP a b f == RightAngle)%angle.
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.extend_point AB a b) as c.
    euclid_apply (proposition_11 a c b AB) as f.
    exists f.
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_12 : forall (a b c : Point) (AB : Line), 
    DistinctPointsOnL a b AB /\ ~ (c on_line AB) ->
    exists h : Point, h on_line AB /\ ((AnglePPP a h c == RightAngle)%angle \/ (AnglePPP b h c == RightAngle)%angle).
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.point_opposite_side AB c) as d.
    euclid_apply (ConstructionRules.circle_from_points c d) as EFG.
    euclid_apply (ConstructionRules.intersections_circle_line EFG AB) as e g.
    euclid_apply (proposition_10 e g) as h.
    euclid_apply (ConstructionRules.line_from_points c g) as CG.
    euclid_apply (ConstructionRules.line_from_points c h) as CH.
    euclid_apply (ConstructionRules.line_from_points c e) as CE.
    exists h.
    euclid_apply (proposition_8 h c g h c e CH CG AB CH CE AB).
    euclid_case (a = h).
    + euclid_apply (TransferInferences.perpendicular_if e g h c AB).
       euclid_trivial.
    + euclid_case (SameSide a g CH).
       - euclid_apply (TransferInferences.perpendicular_if g e h c AB). 
          euclid_trivial.
       - euclid_apply (TransferInferences.perpendicular_if e g h c AB).
          euclid_trivial.
all: fail. Admitted.


Theorem proposition_13 : forall (a b c d : Point) (AB CD : Line), 
    AB <> CD /\ DistinctPointsOnL a b AB /\ DistinctPointsOnL c d CD /\ Between d b c  ->
    (angle2real (AnglePPP c b a)) + (angle2real (AnglePPP a b d)) = (angle2real RightAngle) + (angle2real RightAngle).
Proof.
    euclid_intros.
    euclid_case (AnglePPP c b a == AnglePPP a b d)%angle.
    + euclid_apply (TransferInferences.perpendicular_if c d b a CD).
       euclid_trivial.
    + euclid_apply (proposition_11' d c b a CD) as e. 
       euclid_apply (ConstructionRules.line_from_points b e) as BE. 
       euclid_trivial.
all: fail. Admitted.


Theorem proposition_14 : forall (a b c d : Point) (AB BC BD : Line), 
    DistinctPointsOnL a b AB /\ DistinctPointsOnL b c BC /\ DistinctPointsOnL b d BD /\ (OppositeSide c d AB) /\ ~(a on_line BC) /\
    (angle2real (AnglePPP a b c)) + (angle2real (AnglePPP a b d)) = (angle2real RightAngle) + (angle2real RightAngle) ->
    BC = BD.
Proof.
    euclid_intros.
    euclid_contradict.
    euclid_apply (ConstructionRules.extend_point BC c b) as e.
    euclid_apply (proposition_13 a b e c AB BC). 
    euclid_trivial (AnglePPP a b e == AnglePPP a b d)%angle.
    euclid_case  (SameSide a e BD).
    + euclid_apply (TransferInferences.sum_angles_onlyif b a d e AB BD).
        euclid_trivial.
    + euclid_apply (TransferInferences.sum_angles_onlyif b a e d AB BC).
        euclid_trivial.
all: fail. Admitted.


Theorem proposition_14' : forall (a b c d : Point) (AB BC BD : Line), 
    DistinctPointsOnL a b AB /\ DistinctPointsOnL b c BC /\ DistinctPointsOnL b d BD /\ (OppositeSide c d AB) /\
    (angle2real (AnglePPP a b c)) + (angle2real (AnglePPP a b d)) = (angle2real RightAngle) + (angle2real RightAngle) ->
    BC = BD.
Proof.
    euclid_intros.
    euclid_case (a on_line BC).
    + euclid_case (Between c b a). 
        - euclid_contradict.
           euclid_apply (TransferInferences.flat_angle_onlyif a b c).
           euclid_trivial.
        - euclid_contradict.
           euclid_apply (ConstructionRules.extend_point BC c b) as e.
           euclid_trivial (angle2real (AnglePPP a b c) = 0)%angle.
           euclid_trivial (angle2real (AnglePPP a b d) = (angle2real RightAngle) + (angle2real RightAngle)).
           euclid_apply (proposition_13 d b c e BC BD).
           euclid_trivial.
    + euclid_apply (proposition_14 a b c d AB BC BD).
        assumption. 
all: fail. Admitted.


Theorem proposition_15 : forall (a b c d e : Point) (AB CD : Line), 
    DistinctPointsOnL a b AB /\ DistinctPointsOnL c d CD /\ e on_line AB /\ e on_line CD /\ 
    CD <> AB /\ (Between d e c) /\ (Between a e b) ->
    (AnglePPP a e c == AnglePPP d e b)%angle /\ (AnglePPP c e b == AnglePPP a e d)%angle.
Proof.
    euclid_intros.
    euclid_apply (proposition_13 a e c d AB CD). 
    euclid_apply (proposition_13 d e a b CD AB).
    euclid_apply (proposition_13 c e a b CD AB).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_16 : forall (a b c d : Point) (AB BC AC: Line), 
    Triangle a b c AB BC AC /\ (Between b c d) ->
    (AnglePPP a c d > AnglePPP c b a) /\ (AnglePPP a c d > AnglePPP b a c).
Proof.
    euclid_intros.
    split.
    + euclid_apply (proposition_10 b c BC) as e.
       euclid_apply (ConstructionRules.line_from_points a e) as AE.
       euclid_apply (ConstructionRules.extend_point_longer AE a e (SegmentPP a e)) as f'.
       euclid_apply (proposition_3 e f' a e AE AE) as f.
       euclid_apply (ConstructionRules.line_from_points f c) as FC.
       euclid_apply (proposition_15 b c a f e BC AE).
       euclid_apply (proposition_4 e b a e c f BC AB AE BC FC AE).
       euclid_apply (ConstructionRules.extend_point AC a c) as g.
       euclid_apply (TransferInferences.sum_angles_onlyif c b g f BC AC).
       euclid_apply (proposition_15 a g b d c AC BC). 
       euclid_trivial.
    + euclid_apply (proposition_10 a c AC) as e.
       euclid_apply (ConstructionRules.line_from_points b e) as BE.
       euclid_apply (ConstructionRules.extend_point_longer BE b e (SegmentPP b e)) as f'.
       euclid_apply (proposition_3 e f' b e BE BE) as f.
       euclid_apply (ConstructionRules.line_from_points f c) as FC.
       euclid_apply (proposition_15 a c b f e AC BE).
       euclid_apply (proposition_4 e a b e c f AC AB BE AC FC BE).
       euclid_apply (TransferInferences.sum_angles_onlyif c a d f AC BC).
       euclid_trivial.
all: fail. Admitted.


Theorem proposition_17 : forall (a b c : Point) (AB BC AC : Line), 
    Triangle a b c AB BC AC ->
    (angle2real (AnglePPP a b c)) + (angle2real (AnglePPP b c a))  < (angle2real RightAngle) + (angle2real RightAngle).
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.extend_point BC b c) as d.
    euclid_apply (proposition_16 a b c d AB BC AC).
    euclid_apply (proposition_13 a c b d AC BC).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_18 : forall (a b c : Point) (AB BC AC : Line),
    Triangle a b c AB BC AC /\ (SegmentPP a c > SegmentPP a b) -> 
    (AnglePPP a b c > AnglePPP b c a).
Proof.
    euclid_intros.
    euclid_apply (proposition_3' a c a b AC AB) as d.
    euclid_apply (ConstructionRules.line_from_points b d) as BD.
    euclid_apply (proposition_16 b c d a BC AC BD).
    euclid_apply (proposition_5' a b d AB BD AC).
    euclid_apply (TransferInferences.sum_angles_if b a c d AB BC).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_19 : forall (a b c : Point) (AB BC AC : Line), 
    Triangle a b c AB BC AC /\ (AnglePPP a b c > AnglePPP b c a) -> 
    (SegmentPP a c > SegmentPP a b).
Proof.
    euclid_intros.
    euclid_contradict.
    euclid_case (SegmentPP a c == SegmentPP a b)%segment.
    + euclid_apply (proposition_5' a b c AB BC AC).
       euclid_trivial.
    + euclid_apply (proposition_18 a c b AC BC AB).
       euclid_trivial.
all:fail. Admitted.


Theorem proposition_20 : forall (a b c : Point) (AB BC AC : Line),
    Triangle a b c AB BC AC -> 
    (SegmentPP b a + SegmentPP a c > SegmentPP b c).
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.extend_point_longer AB b a (SegmentPP c a)) as d'.
    euclid_apply (proposition_3' a d' a c AB AC) as d.
    euclid_apply (ConstructionRules.line_from_points d c) as DC.
    euclid_apply (proposition_5' a c d AC DC AB).
    euclid_apply (TransferInferences.sum_angles_onlyif c b d a BC DC).
    euclid_trivial (AnglePPP b c d > AnglePPP a d c).
    euclid_apply (proposition_19 b c d BC DC AB).
    euclid_trivial.
all:fail. Admitted.


Theorem proposition_21 : forall (a b c d : Point) (AB BC AC BD DC : Line),
    Triangle a b c AB BC AC /\ (SameSide a d BC) /\ (SameSide c d AB) /\ (SameSide b d AC) /\
    DistinctPointsOnL b d BD /\ DistinctPointsOnL d c DC ->
    (SegmentPP b d + SegmentPP d c < SegmentPP b a + SegmentPP a c) /\ 
    (AnglePPP b d c > AnglePPP b a c).
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.intersection_lines BD AC) as e.
    euclid_apply (proposition_20 a b e AB BD AC).
    euclid_trivial (SegmentPP b a + SegmentPP a c > SegmentPP b e + SegmentPP e c).
    euclid_apply (proposition_20 e d c BD DC AC).
    euclid_trivial (SegmentPP c e + SegmentPP e b > SegmentPP c d + SegmentPP d b).
    split.
    + euclid_trivial.
    + euclid_apply (proposition_16 c e d b AC BD DC).
       euclid_apply (proposition_16 b a e c AB AC BD).
       euclid_trivial.
all: fail. Admitted.


Theorem proposition_22 : forall (a0 a1 b0 b1 c0 c1 : Point) (A B C : Line),
    DistinctPointsOnL a0 a1 A /\ DistinctPointsOnL b0 b1 B /\ DistinctPointsOnL c0 c1 C /\
    (SegmentPP a0 a1 + SegmentPP b0 b1 > SegmentPP c0 c1) /\
    (SegmentPP a0 a1 + SegmentPP c0 c1 > SegmentPP b0 b1) /\
    (SegmentPP b0 b1 + SegmentPP c0 c1 > SegmentPP a0 a1) ->
    exists (k f g : Point), (SegmentPP f k == SegmentPP a0 a1)%segment /\
    (SegmentPP f g == SegmentPP b0 b1)%segment /\ (SegmentPP k g == SegmentPP c0 c1)%segment. 
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.point) as d.
    euclid_apply (ConstructionRules.distinct_point d) as e'.
    euclid_apply (ConstructionRules.line_from_points d e') as DE.
    euclid_apply (ConstructionRules.extend_point_longer DE d e' (SegmentPP a0 a1)) as e''.
    euclid_apply (ConstructionRules.extend_point_longer DE d e'' (SegmentPP b0 b1)) as e'''.
    euclid_apply (ConstructionRules.extend_point_longer DE d e''' (SegmentPP c0 c1)) as e.
    euclid_apply (proposition_3' d e a0 a1 DE A) as f.
    euclid_apply (proposition_3' f e b0 b1 DE B) as g.
    euclid_apply (proposition_3' g e c0 c1 DE C) as h.
    euclid_apply (ConstructionRules.circle_from_points f d) as DKL.
    euclid_apply (ConstructionRules.circle_from_points g h) as KLH.
    euclid_apply (ConstructionRules.intersection_circle_line_extending_points KLH DE g h) as i.
    assert (i in_circle DKL).  (* not easy to prove the two circles intersect *)
    {
        euclid_case (SegmentPP b0 b1 == SegmentPP c0 c1)%segment.
        + euclid_trivial.
        + euclid_apply (TransferInferences.point_in_circle_if f d i DKL).
           assumption.
    }
    euclid_apply (DiagrammaticInferences.intersection_circle_circle_1 i h KLH DKL).
    euclid_apply (ConstructionRules.intersection_circles KLH DKL) as k.
    exists k.
    exists f.
    exists g.
    euclid_apply (TransferInferences.point_on_circle_onlyif f d k DKL).
    euclid_apply (TransferInferences.point_on_circle_onlyif g k h KLH).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_22' : forall (a0 a1 b0 b1 c0 c1 f e : Point) (A B C DE : Line), 
    DistinctPointsOnL a0 a1 A /\ DistinctPointsOnL b0 b1 B /\ DistinctPointsOnL c0 c1 C /\ DistinctPointsOnL f e DE /\
    (SegmentPP a0 a1 + SegmentPP b0 b1 > SegmentPP c0 c1) /\
    (SegmentPP a0 a1 + SegmentPP c0 c1 > SegmentPP b0 b1) /\
    (SegmentPP b0 b1 + SegmentPP c0 c1 > SegmentPP a0 a1) ->
    exists (k g : Point), g on_line DE /\ ~(Between g f e) /\ 
    (SegmentPP f k == SegmentPP a0 a1)%segment /\
    (SegmentPP f g == SegmentPP b0 b1)%segment /\ (SegmentPP k g == SegmentPP c0 c1)%segment. 
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.extend_point_longer DE f e (SegmentPP b0 b1)) as e'.
    euclid_apply (ConstructionRules.extend_point_longer DE f e' (SegmentPP c0 c1)) as e''.
    euclid_apply (proposition_3' f e'' a0 a1 DE A) as d.
    euclid_apply (proposition_3' f e'' b0 b1 DE B) as g.
    euclid_apply (proposition_3' g e'' c0 c1 DE C) as h.
    euclid_apply (ConstructionRules.circle_from_points f d) as DKL.
    euclid_apply (ConstructionRules.circle_from_points g h) as KLH.
    euclid_apply (ConstructionRules.intersection_circle_line_extending_points KLH DE g h) as i.
    assert (i in_circle DKL).
    {
        euclid_case (SegmentPP b0 b1 == SegmentPP c0 c1)%segment.
        + euclid_trivial.
        + euclid_apply (TransferInferences.point_in_circle_if f d i DKL).
           assumption.
    }
    euclid_apply (DiagrammaticInferences.intersection_circle_circle_1 i h KLH DKL).
    euclid_apply (ConstructionRules.intersection_circles KLH DKL) as k.
    exists k.
    exists g.
    euclid_apply (TransferInferences.point_on_circle_onlyif f d k DKL).
    euclid_apply (TransferInferences.point_on_circle_onlyif g k h KLH).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_22'' : forall (a0 a1 b0 b1 c0 c1 f e x : Point) (A B C DE : Line), 
    DistinctPointsOnL a0 a1 A /\ DistinctPointsOnL b0 b1 B /\ DistinctPointsOnL c0 c1 C /\ DistinctPointsOnL f e DE /\ ~(x on_line DE) /\
    (SegmentPP a0 a1 + SegmentPP b0 b1 > SegmentPP c0 c1) /\
    (SegmentPP a0 a1 + SegmentPP c0 c1 > SegmentPP b0 b1) /\
    (SegmentPP b0 b1 + SegmentPP c0 c1 > SegmentPP a0 a1) ->
    exists (k g : Point), g on_line DE /\ ~(Between g f e) /\ (SameSide k x DE) /\
    (SegmentPP f k == SegmentPP a0 a1)%segment /\
    (SegmentPP f g == SegmentPP b0 b1)%segment /\ (SegmentPP k g == SegmentPP c0 c1)%segment. 
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.extend_point_longer DE f e (SegmentPP b0 b1)) as e'.
    euclid_apply (ConstructionRules.extend_point_longer DE f e' (SegmentPP c0 c1)) as e''.
    euclid_apply (proposition_3' f e'' a0 a1 DE A) as d.
    euclid_apply (proposition_3' f e'' b0 b1 DE B) as g.
    euclid_apply (proposition_3' g e'' c0 c1 DE C) as h.
    euclid_apply (ConstructionRules.circle_from_points f d) as DKL.
    euclid_apply (ConstructionRules.circle_from_points g h) as KLH.
    euclid_apply (ConstructionRules.intersection_circle_line_extending_points KLH DE g h) as i.
    assert (i in_circle DKL).
    {
        euclid_case (SegmentPP b0 b1 == SegmentPP c0 c1)%segment.
        + euclid_trivial.
        + euclid_apply (TransferInferences.point_in_circle_if f d i DKL).
           assumption.
    }
    euclid_apply (DiagrammaticInferences.intersection_circle_circle_1 i h KLH DKL).
    euclid_apply (ConstructionRules.intersection_same_side KLH DKL x g f) as k.
    exists k.
    exists g.
    euclid_apply (TransferInferences.point_on_circle_onlyif f d k DKL).
    euclid_apply (TransferInferences.point_on_circle_onlyif g k h KLH).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_23 : forall (a b c d e : Point) (AB CD CE : Line),
    DistinctPointsOnL a b AB /\ RectilinearAngle d c e CD CE /\ ~(d on_line CE) ->
    exists f : Point, f <> a /\ (AnglePPP f a b == AnglePPP d c e)%angle.
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.line_from_points d e) as DE.
    euclid_apply (proposition_20 c d e CD DE CE).
    euclid_apply (proposition_20 d e c DE CE CD).
    euclid_apply (proposition_20 e c d CE CD DE).
    euclid_apply (proposition_22' c d c e e d a b CD CE DE AB) as f g.
    euclid_apply (ConstructionRules.line_from_points a f) as FA.
    euclid_apply (ConstructionRules.line_from_points f g) as FG.
    euclid_apply (proposition_8 c d e a f g CD DE CE FA FG AB).
    exists f.
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_23' : forall (a b c d e : Point) (AB CD CE : Line),
    DistinctPointsOnL a b AB /\ RectilinearAngle d c e CD CE ->
    exists f : Point, f <> a /\ (AnglePPP f a b == AnglePPP d c e)%angle.
Proof.
    euclid_intros.
    euclid_case (d on_line CE).
    + euclid_case (Between d c e). 
        - (* pi *)
           euclid_apply (ConstructionRules.extend_point AB b a) as f.
           exists f. 
           euclid_trivial.
        - (* 0 *)
           exists b.
           euclid_trivial. 
    + euclid_apply (proposition_23 a b c d e AB CD CE) as f.
       exists f.
       euclid_trivial.
all: fail. Admitted.


Theorem proposition_23'' : forall (a b c d e x : Point) (AB CD CE : Line), 
    DistinctPointsOnL a b AB /\ RectilinearAngle d c e CD CE /\ ~(x on_line AB) ->
    exists f : Point, f <> a /\ ~(SameSide f x AB) /\ (AnglePPP f a b == AnglePPP d c e)%angle.
Proof.
    euclid_intros.
    euclid_case (d on_line CE).
    + euclid_case (Between d c e).
        - euclid_apply (ConstructionRules.extend_point AB b a) as f.
           exists f. 
           euclid_trivial.
        - exists b.
           euclid_trivial. 
    + euclid_apply (ConstructionRules.line_from_points d e) as DE.
        euclid_apply (proposition_20 c d e CD DE CE).
        euclid_apply (proposition_20 d e c DE CE CD).
        euclid_apply (proposition_20 e c d CE CD DE).
        euclid_apply (ConstructionRules.point_opposite_side AB x) as y.
        euclid_apply (proposition_22'' c d c e e d a b y CD CE DE AB) as f g.
        euclid_apply (ConstructionRules.line_from_points a f) as AF.
        euclid_apply (ConstructionRules.line_from_points f g) as FG.
        euclid_apply (proposition_8 c d e a f g CD DE CE AF FG AB).
        exists f.
        euclid_trivial.
all: fail. Admitted.


Theorem proposition_23''' : forall (a b c d e x : Point) (AB CD CE : Line), 
    DistinctPointsOnL a b AB /\ RectilinearAngle d c e CD CE /\ ~(x on_line AB) ->
    exists f : Point, f <> a /\ (f on_line AB \/ SameSide f x AB) /\ (AnglePPP f a b == AnglePPP d c e)%angle.
Proof.
    euclid_intros.
    euclid_case (d on_line CE).
    + euclid_case (Between d c e).
        - euclid_apply (ConstructionRules.extend_point AB b a) as f.
           exists f. 
           euclid_trivial.
        - exists b.
           euclid_trivial. 
    + euclid_apply (ConstructionRules.line_from_points d e) as DE.
        euclid_apply (proposition_20 c d e CD DE CE).
        euclid_apply (proposition_20 d e c DE CE CD).
        euclid_apply (proposition_20 e c d CE CD DE).
        euclid_apply (proposition_22'' c d c e e d a b x CD CE DE AB) as f g.
        euclid_apply (ConstructionRules.line_from_points a f) as AF.
        euclid_apply (ConstructionRules.line_from_points f g) as FG.
        euclid_apply (proposition_8 c d e a f g CD DE CE AF FG AB).
        exists f.
        euclid_apply (ConstructionRules.line_from_points a f) as AF.
        euclid_apply (TransferInferences.equal_angles a f f g b AF AB).
        euclid_trivial.
all: fail. Admitted.


Theorem proposition_24 : forall (a b c d e f : Point) (AB BC AC DE EF DF : Line),
    Triangle a b c AB BC AC /\ Triangle d e f DE EF DF /\ 
    (SegmentPP a b == SegmentPP d e)%segment /\  (SegmentPP a c == SegmentPP d f)%segment /\
    (AnglePPP b a c > AnglePPP e d f) ->
    (SegmentPP b c > SegmentPP e f).
Proof.
    euclid_intros.
    euclid_apply (proposition_23''' d e a b c f DE AB AC) as g'.
    euclid_apply (ConstructionRules.line_from_points d g') as DG.
    euclid_apply (ConstructionRules.extend_point_longer DG d g' (SegmentPP a c)) as g''.
    euclid_apply (proposition_3' d g'' a c DG AC) as g.
    euclid_apply (ConstructionRules.line_from_points e g) as EG.
    euclid_apply (ConstructionRules.line_from_points f g) as FG.
    euclid_case (Between e d g).
    + euclid_apply (proposition_17 c b a BC AB AC). 
       euclid_trivial.
    + euclid_apply (proposition_4 a b c d e g AB BC AC DE EG DG).
       euclid_case (g on_line EF).
       - euclid_trivial (Between e f g).
          euclid_trivial (SegmentPP e g > SegmentPP e f).
          euclid_trivial.
       - euclid_apply (proposition_5' d g f DG FG DF).
          euclid_case (SameSide d e FG).
          * euclid_apply (TransferInferences.sum_angles_onlyif g d f e DG FG). 
            euclid_trivial (AnglePPP d f g > AnglePPP e g f).
            euclid_apply (TransferInferences.sum_angles_onlyif f e g d EF FG). 
            euclid_trivial (AnglePPP e f g > AnglePPP e g f).
            euclid_apply (proposition_19 e f g EF FG EG).
            euclid_trivial.
all: fail. Admitted.


Theorem proposition_25 : forall (a b c d e f : Point) (AB BC AC DE EF DF : Line), 
    Triangle a b c AB BC AC /\ Triangle d e f DE EF DF /\
    (SegmentPP a b == SegmentPP d e)%segment /\  (SegmentPP a c == SegmentPP d f)%segment /\
    (SegmentPP b c > SegmentPP e f) ->
    (AnglePPP b a c > AnglePPP e d f).
Proof.
    euclid_intros.
    euclid_contradict.
    euclid_case (AnglePPP b a c == AnglePPP e d f)%angle.
    + euclid_apply (proposition_4 a b c d e f AB BC AC DE EF DF).
        euclid_trivial.
    + euclid_trivial (AnglePPP b a c < AnglePPP e d f).
        euclid_apply (proposition_24 d e f a b c DE EF DF AB BC AC).
        euclid_trivial.
all: fail. Admitted.


Theorem proposition_26 : forall (a b c d e f : Point) (AB BC AC DE EF DF : Line),
    Triangle a b c AB BC AC /\ Triangle d e f DE EF DF /\
    (AnglePPP a b c == AnglePPP d e f)%angle /\ (AnglePPP b c a == AnglePPP e f d)%angle /\
    ((SegmentPP b c == SegmentPP e f)%segment \/ (SegmentPP a b == SegmentPP d e)%segment) ->
    (SegmentPP a b == SegmentPP d e)%segment /\ (SegmentPP b c == SegmentPP e f)%segment /\
    (SegmentPP a c == SegmentPP d f)%segment /\ (AnglePPP b a c == AnglePPP e d f)%angle.
Proof.
    euclid_intros.
    destruct H.
    + euclid_split.
        {
             euclid_contradict.
             euclid_case (SegmentPP a b > SegmentPP d e).
             - euclid_apply (proposition_3' b a e d AB DE) as g.
                euclid_apply (ConstructionRules.line_from_points g c) as GC.
                euclid_apply (proposition_4 b g c e d f AB GC BC DE DF EF).
                euclid_apply (TransferInferences.sum_angles_onlyif c b a g BC AC).
                euclid_trivial.
             - euclid_case (SegmentPP a b < SegmentPP d e).
                * euclid_apply (proposition_3' e d b a DE AB) as g.
                  euclid_apply (ConstructionRules.line_from_points g f) as GF.
                  euclid_apply (proposition_4 e g f b a c DE GF EF AB AC BC).
                  euclid_apply (TransferInferences.sum_angles_onlyif f e d g EF DF).
                  euclid_trivial.
                * euclid_trivial.
        }
        euclid_apply (proposition_4 b a c e d f AB AC BC DE DF EF). 
        euclid_trivial.
    + assert ((SegmentPP b c == SegmentPP e f)%segment). 
        {
             euclid_contradict.
             euclid_case (SegmentPP b c > SegmentPP e f).
             - euclid_apply (proposition_3' b c e f BC EF) as h.
                euclid_apply (ConstructionRules.line_from_points a h) as AH.
                euclid_apply (proposition_4 b a h e d f AB AH BC DE DF EF).
                euclid_apply (proposition_16 a c h b AC BC AH).
                euclid_trivial.
             - euclid_case (SegmentPP b c < SegmentPP e f).
                * euclid_apply (proposition_3' e f b c EF BC) as h.
                  euclid_apply (ConstructionRules.line_from_points d h) as DH.
                  euclid_apply (proposition_4 e d h b a c DE DH EF AB AC BC).
                  euclid_apply (proposition_16 d f h e DF EF DH).
                  euclid_trivial.
                * euclid_trivial.
        }
        euclid_apply (proposition_4 b a c e d f AB AC BC DE DF EF). 
        euclid_trivial.
all: fail. Admitted.


Theorem proposition_27 : forall (a b c d e f : Point) (AB CD EF : Line), 
    DistinctPointsOnL a b AB /\ DistinctPointsOnL c d CD /\ DistinctPointsOnL e f EF /\
    (Between a e b) /\ (Between c f d) /\  (SameSide b d EF) /\
    (AnglePPP a e f == AnglePPP e f d)%angle -> 
    ~(IntersectsLL AB CD).
Proof.
    euclid_intros.
    euclid_contradict.
    euclid_apply (ConstructionRules.intersection_lines AB CD) as g.
    euclid_case (SameSide g b EF).
    + euclid_apply (proposition_16 f g e a CD AB EF).
       euclid_trivial.
    + euclid_apply (proposition_16 e g f d AB CD EF).
        euclid_trivial.
all: fail. Admitted.


Theorem proposition_27' : forall (a d e f : Point) (AB CD EF : Line), 
    DistinctPointsOnL a e AB /\ DistinctPointsOnL f d CD /\ DistinctPointsOnL e f EF /\
    OppositeSide a d EF /\ (AnglePPP a e f == AnglePPP e f d)%angle -> 
    ~(IntersectsLL AB CD).
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.extend_point AB a e) as b.
    euclid_apply (ConstructionRules.extend_point CD d f) as c.
    euclid_apply (proposition_27 a b c d e f AB CD EF).
    euclid_trivial.
all: fail. Admitted.

Theorem proposition_28 : forall (a b c d e f g h : Point) (AB CD EF : Line), 
    DistinctPointsOnL a b AB /\ DistinctPointsOnL c d CD /\ DistinctPointsOnL e f EF /\ 
    (Between a g b)  /\ (Between c h d) /\ (Between e g h) /\ (Between g h f) /\ (SameSide b d EF) /\
    ((AnglePPP e g b == AnglePPP g h d)%angle \/ (angle2real (AnglePPP b g h) + angle2real (AnglePPP g h d) = RightAngle + RightAngle)) -> 
    ~(IntersectsLL AB CD).
Proof.
    euclid_intros.
    destruct H.
    + euclid_apply (proposition_15 a b e h g AB EF).
       euclid_apply (proposition_27 a b c d g h AB CD EF).
       assumption.
    + euclid_apply (proposition_13 h g a b EF AB).
       euclid_trivial (AnglePPP a g h == AnglePPP g h d)%angle.
       euclid_apply (proposition_27 a b c d g h AB CD EF).
       assumption.
all: fail. Admitted.


Theorem proposition_29 : forall (a b c d e f g h : Point) (AB CD EF : Line), 
    DistinctPointsOnL a b AB /\ DistinctPointsOnL c d CD /\ DistinctPointsOnL e f EF /\
    (Between a g b) /\ (Between c h d) /\ (Between e g h) /\ (Between g h f) /\ (SameSide b d EF) /\
    ~(IntersectsLL AB CD) ->
    (AnglePPP a g h == AnglePPP g h d)%angle /\ (AnglePPP e g b == AnglePPP g h d)%angle /\ 
    (angle2real (AnglePPP b g h) + angle2real (AnglePPP g h d) = RightAngle + RightAngle).
Proof.
    euclid_intros.
    euclid_split.
    { 
        euclid_contradict.
        euclid_case (AnglePPP a g h > AnglePPP g h d).
        + euclid_trivial (AnglePPP a g h + AnglePPP b g h > AnglePPP b g h + AnglePPP g h d).
           euclid_apply (proposition_13 h g a b EF AB).
           euclid_trivial (AnglePPP b g h + AnglePPP g h d < RightAngle + RightAngle).
           euclid_trivial.
        + euclid_case (AnglePPP g h d > AnglePPP a g h).
            - euclid_trivial (AnglePPP c h g + AnglePPP g h d > AnglePPP a g h + AnglePPP c h g).
               euclid_apply (proposition_13 g h c d EF CD).
               euclid_trivial (AnglePPP a g h + AnglePPP c h g < RightAngle + RightAngle).
               euclid_trivial.
            - euclid_trivial.
    }
    euclid_apply (proposition_15 a b e h g AB EF).
    euclid_apply (proposition_13 b g e h AB EF).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_29' : forall (a b c d e g h : Point) (AB CD EF : Line), 
    DistinctPointsOnL a b AB /\ DistinctPointsOnL c d CD /\ DistinctPointsOnL g h EF /\
    (Between a g b) /\ (Between c h d) /\ (Between e g h) /\ (SameSide b d EF) /\
    ~(IntersectsLL AB CD) ->
    (AnglePPP a g h == AnglePPP g h d)%angle /\ (AnglePPP e g b == AnglePPP g h d)%angle /\ 
    (angle2real (AnglePPP b g h) + angle2real (AnglePPP g h d) = RightAngle + RightAngle).
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.extend_point EF g h) as f.
    euclid_apply (proposition_29 a b c d e f g h AB CD EF).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_29'' : forall (a b d g h : Point) (AB CD GH : Line), 
    DistinctPointsOnL a b AB /\ DistinctPointsOnL h d CD /\ DistinctPointsOnL g h GH /\
    (Between a g b) /\ (SameSide b d GH) /\ ~(IntersectsLL AB CD) ->
    (AnglePPP a g h == AnglePPP g h d)%angle /\ 
    (angle2real (AnglePPP b g h) + angle2real (AnglePPP g h d) = RightAngle + RightAngle).
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.extend_point GH g h) as f.
    euclid_apply (ConstructionRules.extend_point GH h g) as e.
    euclid_apply (ConstructionRules.extend_point CD d h) as c.
    euclid_apply (proposition_29 a b c d e f g h AB CD GH).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_29''' : forall (a d g h : Point) (AB CD GH : Line), 
    DistinctPointsOnL a g AB /\ DistinctPointsOnL h d CD /\ DistinctPointsOnL g h GH /\
    OppositeSide a d GH /\ ~(IntersectsLL AB CD) ->
    (AnglePPP a g h == AnglePPP g h d)%angle.
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.extend_point AB a g) as b.
    euclid_apply (proposition_29'' a b d g h AB CD GH).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_29'''' : forall (b d e g h : Point) (AB CD EF : Line), 
    DistinctPointsOnL g b AB /\ DistinctPointsOnL h d CD /\ DistinctPointsOnL e h EF /\
    Between e g h  /\ SameSide b d EF /\ ~(IntersectsLL AB CD) ->
    (AnglePPP e g b == AnglePPP g h d)%angle.
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.extend_point AB b g) as a.
    euclid_apply (ConstructionRules.extend_point CD d h) as c.
    euclid_apply (ConstructionRules.extend_point EF g h) as f.
    euclid_apply (proposition_29 a b c d e f g h AB CD EF).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_29''''' : forall (b d g h : Point) (AB CD EF : Line), 
    DistinctPointsOnL g b AB /\ DistinctPointsOnL h d CD /\ DistinctPointsOnL g h EF /\
    SameSide b d EF /\ ~(IntersectsLL AB CD) ->
    (angle2real (AnglePPP b g h) + angle2real (AnglePPP g h d) = RightAngle + RightAngle).
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.extend_point AB b g) as a.
    euclid_apply (ConstructionRules.extend_point CD d h) as c.
    euclid_apply (ConstructionRules.extend_point EF g h) as f.
    euclid_apply (ConstructionRules.extend_point EF h g) as e.
    euclid_apply (proposition_29 a b c d e f g h AB CD EF).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_30 : forall (AB CD EF : Line), 
    AB <> CD /\ CD <> EF /\ EF <> AB /\ ~(IntersectsLL AB EF) /\ ~(IntersectsLL CD EF) ->
    ~(IntersectsLL AB CD).
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.point_on_line AB) as g.
    euclid_apply (ConstructionRules.distinct_point_on_line CD g) as k.
    euclid_apply (ConstructionRules.line_from_points g k) as GK.
    euclid_apply (ConstructionRules.intersection_lines EF GK) as h.
    euclid_apply (ConstructionRules.distinct_point_on_line AB g) as a.
    euclid_apply (ConstructionRules.extend_point AB a g) as b.
    euclid_apply (point_on_line_same_side GK EF a) as e.
    euclid_apply (ConstructionRules.extend_point EF e h) as f.
    euclid_apply (point_on_line_same_side GK CD a) as c.
    euclid_apply (ConstructionRules.extend_point CD c k) as d.
    euclid_case (Between g h k).
    + euclid_apply (proposition_29'' a b f g h AB EF GK).
       euclid_apply (proposition_29' e f c d g h k EF CD GK).
       euclid_trivial (AnglePPP a g k == AnglePPP g k d)%angle.
       euclid_apply (proposition_27 a b c d g k AB CD GK).
       assumption.
    + euclid_case (Between g k h).
        - euclid_apply (proposition_29'' a b f g h AB EF GK).
           euclid_apply (proposition_29' c d e f g k h CD EF GK).
           euclid_trivial (AnglePPP a g k == AnglePPP g k d)%angle.
           euclid_apply (proposition_27 a b c d g k AB CD GK).
           assumption.
        - euclid_trivial (Between k g h).
           euclid_apply (proposition_29'' d c e k h CD EF GK).
           euclid_apply (proposition_29' b a f e k g h AB EF GK).
           euclid_trivial (AnglePPP a g k == AnglePPP g k d)%angle.
           euclid_apply (proposition_27 a b c d g k AB CD GK).
           assumption.
all: fail. Admitted.


Theorem proposition_31 : forall (a b c : Point) (BC : Line),
    DistinctPointsOnL b c BC /\ ~(a on_line BC) ->
    exists EF : Line, a on_line EF /\ ~(IntersectsLL EF BC).
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.point_between_points BC b c) as d.
    euclid_apply (ConstructionRules.line_from_points a d) as AD.
    euclid_apply (proposition_23''' a d d a c b AD AD BC) as e.
    euclid_apply (ConstructionRules.line_from_points e a) as EF.
    euclid_apply (ConstructionRules.extend_point EF e a) as f.
    exists EF.
    destruct He1.
    + euclid_trivial.
    + euclid_apply (proposition_27 e f b c a d EF BC AD).
       euclid_trivial.
all: fail. Admitted.


Theorem proposition_32 : forall (a b c d : Point) (AB BC AC : Line),
    Triangle a b c AB BC AC /\ (Between b c d) ->
    (angle2real (AnglePPP a c d) = angle2real (AnglePPP c a b) + angle2real (AnglePPP a b c)) /\
    (angle2real (AnglePPP a b c) + angle2real (AnglePPP b c a) + angle2real (AnglePPP c a b) = angle2real RightAngle + angle2real RightAngle).
Proof.
    euclid_intros.
    euclid_split.
    +
        euclid_apply (proposition_31 c a b AB) as CE.
        euclid_apply (ConstructionRules.point_on_line_same_side BC CE a) as e.
        euclid_apply (proposition_29''' b e a c AB CE AC).
        euclid_apply (proposition_29'''' e a d c b CE AB BC).
        euclid_apply (TransferInferences.sum_angles_onlyif c a d e AC BC).
        euclid_trivial.
    + euclid_apply (proposition_13 a c b d AC BC).
       euclid_trivial.
all: fail. Admitted.


Theorem proposition_33 : forall (a b c d : Point) (AB CD AC BD : Line),
    DistinctPointsOnL a b AB /\ DistinctPointsOnL c d CD /\ DistinctPointsOnL a c AC /\ DistinctPointsOnL b d BD /\ 
    (SameSide a c BD) /\ ~(IntersectsLL AB CD) /\ (SegmentPP a b == SegmentPP c d)%segment ->
    AC <> BD /\ ~(IntersectsLL AC BD) /\ (SegmentPP a c == SegmentPP b d)%segment.
Proof.
    euclid_intros.
    euclid_apply  (ConstructionRules.line_from_points b c) as BC.
    euclid_apply (proposition_29''' a d b c AB CD BC).
    euclid_apply (proposition_4 c b d b c a BC BD CD BC AC AB).
    euclid_apply (proposition_27' a d c b AC BD BC).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_34 : forall (a b c d : Point) (AB CD AC BD BC : Line),
    Parallelogram a b c d AB CD AC BD /\ DistinctPointsOnL b c BC ->
    (SegmentPP a b == SegmentPP c d)%segment /\ (SegmentPP a c == SegmentPP b d)%segment /\
    (AnglePPP a b d == AnglePPP a c d)%angle /\ (AnglePPP b a c  == AnglePPP c d b)%angle /\
    (AreaPPP a b c == AreaPPP d c b)%area.
Proof.
    euclid_intros.
    euclid_apply (proposition_29''' a d b c AB CD BC).
    euclid_apply (proposition_29''' a d c b AC BD BC).
    euclid_apply (proposition_26 a b c d c b AB BC AC CD BC BD).
    euclid_apply (TransferInferences.sum_angles_onlyif b a d c AB BD).
    euclid_apply (TransferInferences.sum_angles_onlyif c d a b CD AC).
    euclid_apply (MetricInferences.area_congruence a b c d c b).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_34' : forall (a b c d : Point) (AB CD AC BD : Line),
    Parallelogram a b c d AB CD AC BD ->
    (SegmentPP a b == SegmentPP c d)%segment /\ (SegmentPP a c == SegmentPP b d)%segment /\
    (AnglePPP a b d == AnglePPP a c d)%angle /\ (AnglePPP b a c  == AnglePPP c d b)%angle.
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.line_from_points b c) as BC.
    euclid_apply (proposition_34 a b c d AB CD AC BD BC).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_35 : forall (a b c d e f g : Point) (AF BC AB CD EB FC : Line),
    Parallelogram a d b c AF BC AB CD /\ Parallelogram e f b c AF BC EB FC /\ 
    Between a d e /\ Between d e f /\ g on_line CD /\ g on_line EB ->
    area2real (AreaPPP a b d) + area2real (AreaPPP d b c) = area2real (AreaPPP e b c) + area2real (AreaPPP e c f).
Proof.
    euclid_intros.
    euclid_apply (proposition_34' a d b c AF BC AB CD).
    euclid_apply (proposition_34' e f b c AF BC EB FC).
    euclid_trivial (SegmentPP a d == SegmentPP e f)%segment.
    euclid_trivial (SegmentPP a e == SegmentPP d f)%segment.
    euclid_apply (proposition_29'''' c b f d a CD AB AF).
    euclid_apply (proposition_4 a e b d f c AF EB AB AF FC CD).
    euclid_apply (MetricInferences.area_congruence a e b d f c).
    euclid_apply (TransferInferences.sum_areas_if a e d b AF).
    euclid_apply (TransferInferences.sum_areas_if f d e c AF).
    euclid_apply (TransferInferences.sum_areas_if b e g d EB).
    euclid_apply (TransferInferences.sum_areas_if c d g e CD).
    euclid_trivial (area2real (AreaPPP a d b) + area2real (AreaPPP b g d) = area2real (AreaPPP e c f) + area2real (AreaPPP c g e)).
    euclid_trivial (area2real (AreaPPP a d b) + area2real (AreaPPP b g d) + area2real (AreaPPP g b c) = area2real (AreaPPP e c f) + area2real (AreaPPP c g e) + area2real (AreaPPP g b c)).
    euclid_apply (TransferInferences.sum_areas_if c d g b CD).
    euclid_apply (TransferInferences.sum_areas_if b e g c EB).
    euclid_trivial. 
all: fail. Admitted.


Theorem proposition_35' : forall (a b c d e f : Point) (AF BC AB CD EB FC : Line),
    Parallelogram a d b c AF BC AB CD /\ Parallelogram e f b c AF BC EB FC ->
    area2real (AreaPPP a b d) + area2real (AreaPPP d b c) = area2real (AreaPPP e b c) + area2real (AreaPPP e c f).
Proof.
    euclid_intros.
    euclid_apply (proposition_34' a d b c AF BC AB CD).
    euclid_apply (proposition_34' e f b c AF BC EB FC).
    euclid_trivial (SegmentPP a d == SegmentPP e f)%segment.
    euclid_case (Between a d f).
    + euclid_apply (ConstructionRules.intersection_lines CD EB) as g. 
        euclid_case (Between a d e).
        - euclid_apply (proposition_35 a b c d e f g AF BC AB CD EB FC).
           assumption.
        - euclid_apply (proposition_29'''' c b f d a CD AB AF).
           euclid_apply (proposition_4 a e b d f c AF EB AB AF FC CD).
           euclid_apply (MetricInferences.area_congruence a e b d f c).
           euclid_case (d = e).
           * euclid_trivial.
           * euclid_trivial (Between a e d).
             euclid_trivial (Between g e b).
             euclid_trivial (area2real (AreaPPP a e b) + area2real (AreaPPP g b c) = area2real (AreaPPP d f c) + area2real (AreaPPP g b c)).
             euclid_apply (TransferInferences.sum_areas_if a d e b AF).
             euclid_apply (TransferInferences.sum_areas_if f e d c AF).
             euclid_apply (TransferInferences.sum_areas_if g b e d EB).
             euclid_apply (TransferInferences.sum_areas_if g c d e CD).
             euclid_apply (TransferInferences.sum_areas_if g c d b CD).
             euclid_apply (TransferInferences.sum_areas_if g b e c EB).
             euclid_trivial.
    + euclid_case (a = e).
       - euclid_trivial (d = f).
          euclid_apply (ConstructionRules.line_from_points a c) as AC.
          euclid_trivial.
       - euclid_trivial (Between e f d).
          euclid_trivial (Between e a d).
          euclid_apply (ConstructionRules.intersection_lines FC AB) as g. 
          euclid_case (Between e f a).
          * euclid_apply (proposition_35 e b c f a d g AF BC EB FC AB CD).
            euclid_trivial.
          * euclid_apply (proposition_29'''' c b d f e FC EB AF).
            euclid_apply (proposition_4 e a b f d c AF AB EB AF CD FC).
            euclid_apply (MetricInferences.area_congruence e a b f d c ).
            euclid_case (f = a).
            {
              euclid_trivial.
            } 
            {
              euclid_trivial (Between e a f).
              euclid_trivial (Between g a b).
              euclid_trivial (area2real (AreaPPP e a b) + area2real (AreaPPP g b c) = area2real (AreaPPP f d c) + area2real (AreaPPP g b c)).
              euclid_apply (TransferInferences.sum_areas_if e f a b AF).
              euclid_apply (TransferInferences.sum_areas_if d a f c AF).
              euclid_apply (TransferInferences.sum_areas_if g b a f AB).
              euclid_apply (TransferInferences.sum_areas_if g c f a FC).
              euclid_apply (TransferInferences.sum_areas_if g c f b FC).
              euclid_apply (TransferInferences.sum_areas_if g b a c AB).
              euclid_trivial.
            }
all: fail. Admitted.


Theorem proposition_36 : forall (a b c d e f g h : Point) (AH BG AB CD EF HG : Line) ,
    Parallelogram a d b c AH BG AB CD /\ Parallelogram e h f g AH BG EF HG /\
    (SegmentPP b c == SegmentPP f g)%segment /\ (Between a d h) /\ (Between a e h) ->
    area2real (AreaPPP a b d) + area2real (AreaPPP d b c) = area2real (AreaPPP e f h) + area2real (AreaPPP h f g).
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.line_from_points b e) as BE.
    euclid_apply (ConstructionRules.line_from_points c h) as CH.
    euclid_apply (proposition_34' e h f g AH BG EF HG).
    euclid_trivial (SegmentPP b c== SegmentPP e h)%segment.
    euclid_apply (proposition_33 e h b c AH BG BE CH).
    euclid_trivial (Parallelogram e h b c AH BG BE CH).
    euclid_apply (proposition_35' a b c d e h AH BG AB CD BE CH).
    euclid_apply (proposition_35' g h e f c b BG AH HG EF CH BE).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_36' : forall (a b c d e f g h : Point) (AH BG AB CD EF HG : Line) ,
    Parallelogram a d b c AH BG AB CD /\ Parallelogram e h f g AH BG EF HG /\
    (SegmentPP b c == SegmentPP f g)%segment ->
    area2real (AreaPPP a b d) + area2real (AreaPPP d b c) = area2real (AreaPPP e f h) + area2real (AreaPPP h f g).
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.line_from_points b e) as BE.
    euclid_apply (ConstructionRules.line_from_points c h) as CH.
    euclid_case (SameSide e b CH).
    + euclid_apply (ConstructionRules.line_from_points h f) as HF.
       euclid_apply (proposition_34 e h f g AH BG EF HG HF).
       euclid_trivial (SegmentPP b c== SegmentPP e h)%segment.
       euclid_apply (proposition_33 e h b c AH BG BE CH).
       euclid_trivial (Parallelogram e h b c AH BG BE CH).
       euclid_apply (proposition_35' a b c d e h AH BG AB CD BE CH). 
       euclid_apply (proposition_35' g h e f c b BG AH HG EF CH BE).
       euclid_trivial.
    + euclid_apply (ConstructionRules.line_from_points b h) as BH.
       euclid_apply (ConstructionRules.line_from_points c e) as CE.
       euclid_apply (ConstructionRules.line_from_points e g) as EG.
       euclid_apply (proposition_34 h e g f AH BG HG EF EG).
       euclid_trivial (SegmentPP b c== SegmentPP e h)%segment.
       euclid_apply (proposition_33 h e b c AH BG BH CE).
       euclid_trivial (Parallelogram h e b c AH BG BH CE).
       euclid_apply (proposition_35' a b c d h e AH BG AB CD BH CE).
       euclid_apply (proposition_35' f e h g c b BG AH EF HG CE BH).
       euclid_trivial.
all: fail. Admitted.


Theorem proposition_37 : forall (a b c d : Point) (AB BC AC BD CD AD : Line),
    Triangle a b c AB BC AC /\ Triangle d b c BD BC CD /\ DistinctPointsOnL a d AD /\
    ~(IntersectsLL AD BC) /\ SameSide d c AB ->
    (AreaPPP a b c == AreaPPP d b c)%area.
Proof.
    euclid_intros.
    euclid_apply (proposition_31 b a c AC) as BE.
    euclid_apply (ConstructionRules.intersection_lines AD BE) as e.
    euclid_apply (proposition_31 c b d BD) as CF.
    euclid_apply (ConstructionRules.intersection_lines AD CF) as f.
    euclid_apply (proposition_35' e b c a d f AD BC BE AC BD CF).
    euclid_apply (proposition_34 e a b c AD BC BE AC AB).
    euclid_apply (proposition_34 f d c b AD BC CF BD CD).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_37' : forall (a b c d : Point) (AB BC AC BD CD AD : Line),
    Triangle a b c AB BC AC /\ Triangle d b c BD BC CD /\ DistinctPointsOnL a d AD /\
    ~(IntersectsLL AD BC) ->
    (AreaPPP a b c == AreaPPP d b c)%area.
Proof.
    euclid_intros.
    euclid_case (SameSide d c AB).
    + euclid_apply (proposition_37 a b c d AB BC AC BD CD AD).
       assumption.
    + euclid_trivial (SameSide a c BD).
       euclid_apply (proposition_37 d b c a BD BC CD AB AC AD).
       euclid_trivial.
all: fail. Admitted.


Theorem proposition_38 : forall (a b c d e f: Point) (AD BF AB AC DE DF : Line),
    a on_line AD /\ d on_line AD /\ Triangle a b c AB BF AC /\ Triangle d e f DE BF DF /\
    ~(IntersectsLL AD BF) /\ (Between b c f) /\ (Between b e f) /\ (SegmentPP b c == SegmentPP e f)%segment ->
    (AreaPPP a b c == AreaPPP d e f)%area.
Proof.
    euclid_intros.
    euclid_apply (proposition_31 b a c AC) as BG.
    euclid_apply (ConstructionRules.intersection_lines AD BG) as g.
    euclid_apply (proposition_31 f d e DE) as FH.
    euclid_apply (ConstructionRules.intersection_lines AD FH) as h.
    euclid_apply (proposition_36' g b c a d e f h AD BF BG AC DE FH).
    euclid_apply (proposition_34 g a b c AD BF BG AC AB).
    euclid_apply (proposition_34 e f d h BF AD DE FH DF).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_39 : forall (a b c d : Point) (AB BC AC BD CD AD : Line) ,
    Triangle a b c AB BC AC /\ Triangle d b c BD BC CD /\ SameSide a d BC /\ SameSide c d AB /\
    (AreaPPP a b c == AreaPPP d b c)%area /\ DistinctPointsOnL a d AD ->
    ~(IntersectsLL AD BC).
Proof.
    euclid_intros.
    euclid_contradict.
    euclid_apply (proposition_31 a b c BC) as AE.
    euclid_apply (ConstructionRules.intersection_lines AE BD) as e.
    euclid_apply (ConstructionRules.line_from_points e c) as EC.
    euclid_apply (proposition_37 a b c e AB BC AC BD EC AE). 
    euclid_trivial (AreaPPP e b c == AreaPPP d b c)%area.
    euclid_trivial.
all: fail. Admitted.

(*
Theorem proposition_39 : forall (a b c d : Point) (AB BC AC BD CD AD : Line) ,
    Triangle a b c AB BC AC /\ Triangle d b c BD BC CD /\ SameSide a d BC /\ 
    (AreaPPP a b c == AreaPPP d b c)%area /\ DistinctPointsOnL a d AD ->
    ~(IntersectsLL AD BC).
Proof.
    euclid_intros.
    euclid_contradict.
    euclid_case (SameSide c d AB).
    + euclid_apply (proposition_31 a b c BC) as AE.
       euclid_apply (ConstructionRules.intersection_lines AE BD) as e.
       euclid_apply (ConstructionRules.line_from_points e c) as EC.
       euclid_apply (proposition_37 a b c e AB BC AC BD EC AE). 
       euclid_trivial (AreaPPP e b c == AreaPPP d b c)%area.
       euclid_trivial.
    + euclid_trivial (SameSide c a BD).
       euclid_apply (proposition_31 d b c BC) as DE.
       euclid_apply (ConstructionRules.intersection_lines DE AB) as e.
       euclid_apply (ConstructionRules.line_from_points e c) as EC.
       euclid_apply (proposition_37 d b c e BD BC CD AB EC DE).
       euclid_trivial (AreaPPP e b c == AreaPPP a b c)%area.
       euclid_trivial.
all: fail. Admitted.
*)


Theorem proposition_40 : forall  (a b c d e : Point) (AB BC AC CD DE AD : Line),
    Triangle a b c AB BC AC /\ Triangle d c e CD BC DE /\ SameSide a d BC /\ (SegmentPP b c == SegmentPP c e)%segment /\
    SameSide c d AB /\ b <> e /\ DistinctPointsOnL a d AD /\ (AreaPPP a b c == AreaPPP d c e)%area ->
    ~(IntersectsLL AD BC).
Proof.
    euclid_intros. 
    euclid_contradict.
    euclid_apply (proposition_31 a b c BC) as AF.
    euclid_apply (ConstructionRules.intersection_lines AF CD) as f.
    euclid_case (a = f).
    + euclid_apply (ConstructionRules.intersection_lines AF DE) as g.
       euclid_apply (ConstructionRules.line_from_points g c) as GC.
       euclid_apply (proposition_38  a b c g c e AF BC AB AC GC DE).
       euclid_trivial (AreaPPP d c e == AreaPPP g c e)%area.
       euclid_trivial.
    + euclid_apply (ConstructionRules.line_from_points f e) as FE.
       euclid_apply (proposition_38  a b c f c e AF BC AB AC CD FE).
       euclid_trivial (AreaPPP d c e == AreaPPP f c e)%area.
       euclid_apply (TransferInferences.degenerated_area_if d f e CD).
       euclid_trivial.
all: fail. Admitted.


(*
Theorem proposition_40 : forall  (a b c d e : Point) (AB BC AC CD DE AD : Line),
    Triangle a b c AB BC AC /\ Triangle d c e CD BC DE /\ SameSide a d BC /\ (SegmentPP b c == SegmentPP c e)%segment /\
    DistinctPointsOnL a d AD /\ (AreaPPP a b c == AreaPPP d c e)%area ->
    ~(IntersectsLL AD BC).
Proof.
    euclid_intros. 
    euclid_case (b = e).
    + euclid_apply (proposition_39 a b c d AB BC AC DE CD AD).
       assumption.
    + euclid_contradict.
       euclid_trivial (Between b c e).
       euclid_case (SameSide c d AB).
       - euclid_apply (proposition_31 a b c BC) as AF.
          euclid_apply (ConstructionRules.intersection_lines AF CD) as f.
          euclid_case (a = f).
          * euclid_apply (ConstructionRules.intersection_lines AF DE) as g.
            euclid_apply (ConstructionRules.line_from_points g c) as GC.
            euclid_apply (proposition_38  a b c g c e AF BC AB AC GC DE).
            euclid_trivial (AreaPPP d c e == AreaPPP g c e)%area.
            euclid_trivial.
          * euclid_apply (ConstructionRules.line_from_points f e) as FE.
            euclid_apply (proposition_38  a b c f c e AF BC AB AC CD FE).
            euclid_trivial (AreaPPP d c e == AreaPPP f c e)%area.
            euclid_apply (TransferInferences.degenerated_area_if d f e CD).
            euclid_trivial.
       - euclid_apply (proposition_31 a b c BC) as AF.
          euclid_apply (ConstructionRules.intersection_lines AF DE) as f.
          euclid_case (a = f).
          * euclid_apply (ConstructionRules.intersection_lines AF CD) as g.
            euclid_apply (ConstructionRules.line_from_points g e) as GE.
            euclid_apply (proposition_38  a b c g c e AF BC AB AC CD GE).
            euclid_trivial (AreaPPP d c e == AreaPPP g c e)%area.
            euclid_trivial.
          * euclid_apply (ConstructionRules.line_from_points f c) as FC.
            euclid_apply (proposition_38 a b c f c e AF BC AB AC FC DE).
            euclid_trivial (AreaPPP d c e == AreaPPP f c e)%area. (* remove *)
            euclid_trivial (area2real (AreaPPP d f c) = 0).
            euclid_apply (TransferInferences.degenerated_area_if c d f CD).
            euclid_trivial.
all: fail. Admitted.
*)

Theorem proposition_41 : forall (a b c d e : Point) (AE BC AB CD BE CE : Line) , 
    Parallelogram a d b c AE BC AB CD /\ Triangle e b c BE BC CE /\ e on_line AE /\ ~(IntersectsLL AE BC) ->
    (area2real (AreaPPP a b c) + area2real (AreaPPP a c d) = area2real (AreaPPP e b c) + area2real (AreaPPP e b c)).
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.line_from_points a c) as AC.
    euclid_case (a = e).
    + euclid_trivial (AreaPPP a b c == AreaPPP e b c)%area.
       euclid_apply (proposition_34 d a c b AE BC CD AB AC).
       euclid_trivial.
    + euclid_apply (proposition_37' a b c e AB BC AC BE CE AE).
       euclid_apply (proposition_34 d a c b AE BC CD AB AC).
       euclid_trivial.
all: fail. Admitted.


Theorem proposition_42 : forall (a b c d1 d2 d3 : Point) (AB BC AC D12 D23: Line),
    Triangle a b c AB BC AC /\ RectilinearAngle d1 d2 d3 D12 D23 /\ 
    angle2real (AnglePPP d1 d2 d3) > 0 /\ angle2real (AnglePPP d1 d2 d3) < RightAngle + RightAngle ->
    exists (f g e c' : Point) (FG EC EF CG : Line),  Parallelogram f g e c' FG EC EF CG /\ 
    (AnglePPP c' e f == AnglePPP d1 d2 d3)%angle /\
    (area2real (AreaPPP f e c') + area2real (AreaPPP f c' g) = area2real (AreaPPP a b c)).
Proof.
    euclid_intros.
    euclid_apply (proposition_10 b c BC) as e.
    euclid_apply (ConstructionRules.line_from_points a e) as AE.
    euclid_apply (proposition_23''' e c d2 d1 d3 a BC D12 D23) as f'.
    euclid_apply (ConstructionRules.line_from_points e f') as EF.
    euclid_apply (proposition_31 a b c BC) as AG.
    euclid_apply (ConstructionRules.intersection_lines AG EF) as f.
    euclid_apply (proposition_31 c e f EF) as CG.
    euclid_apply (ConstructionRules.intersection_lines CG AG) as g.
    euclid_trivial (Parallelogram f g e c AG BC EF CG).
    euclid_apply (proposition_38 a b e a e c AG BC AB AE AE AC).
    euclid_trivial (area2real (AreaPPP a b c) = area2real (AreaPPP a e c) + area2real (AreaPPP a e c)).
    euclid_apply (proposition_41 f e c g a AG BC EF CG AE AC).
    exists f.
    exists g.
    exists e.
    exists c.
    exists AG.
    exists BC.
    exists EF.
    exists CG.
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_42' : forall (a b c d1 d2 d3 e : Point) (AB BC AC D12 D23: Line),
    Triangle a b c AB BC AC /\ RectilinearAngle d1 d2 d3 D12 D23 /\ Between b e c /\ (SegmentPP b e == SegmentPP e c)%segment /\
    angle2real (AnglePPP d1 d2 d3) > 0 /\ angle2real (AnglePPP d1 d2 d3) < RightAngle + RightAngle ->
    exists (f g : Point) (FG EF CG : Line), SameSide a f BC /\ Parallelogram f g e c FG BC EF CG /\ 
    (AnglePPP c e f == AnglePPP d1 d2 d3)%angle /\
    (area2real (AreaPPP f e c) + area2real (AreaPPP f c g) = area2real (AreaPPP a b c)).
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.line_from_points a e) as AE.
    euclid_apply (proposition_23''' e c d2 d1 d3 a BC D12 D23) as f'.
    euclid_apply (ConstructionRules.line_from_points e f') as EF.
    euclid_apply (proposition_31 a b c BC) as AG.
    euclid_apply (ConstructionRules.intersection_lines AG EF) as f.
    euclid_apply (proposition_31 c e f EF) as CG.
    euclid_apply (ConstructionRules.intersection_lines CG AG) as g.
    euclid_trivial (Parallelogram f g e c AG BC EF CG).
    euclid_apply (proposition_38 a b e a e c AG BC AB AE AE AC).
    euclid_trivial (area2real (AreaPPP a b c) = area2real (AreaPPP a e c) + area2real (AreaPPP a e c)).
    euclid_apply (proposition_41 f e c g a AG BC EF CG AE AC).
    exists f.
    exists g.
    exists AG.
    exists EF.
    exists CG.
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_42'' : forall (a b c d1 d2 d3 h i : Point) (AB BC AC D12 D23 HI : Line),
    Triangle a b c AB BC AC /\ RectilinearAngle d1 d2 d3 D12 D23 /\ 
    angle2real (AnglePPP d1 d2 d3) > 0 /\ angle2real (AnglePPP d1 d2 d3) < RightAngle + RightAngle /\
    DistinctPointsOnL h i HI ->
    exists (f g j : Point) (FG FI GJ : Line), Between h i j /\ Parallelogram f g i j FG HI FI GJ /\ 
    (AnglePPP j i f == AnglePPP d1 d2 d3)%angle /\
    (area2real (AreaPPP f i j) + area2real (AreaPPP f j g) = area2real (AreaPPP a b c)).
Proof.
    euclid_intros.
    euclid_apply (proposition_10 b c BC) as e.
    euclid_apply (ConstructionRules.extend_point_longer HI h i (SegmentPP e c)) as i'.
    euclid_apply (proposition_3' i i' e c HI BC) as j.
    euclid_apply (ConstructionRules.extend_point_longer HI i h (SegmentPP e c)) as h'.
    euclid_apply (proposition_3' i h' e c HI BC) as k.
    euclid_apply (proposition_23 k j b a c HI AB BC) as l'.
    euclid_apply (ConstructionRules.line_from_points k l') as KL.
    euclid_apply (ConstructionRules.extend_point_longer KL k l' (SegmentPP a b)) as l''.
    euclid_apply (proposition_3' k l'' b a KL AB) as l.
    euclid_apply (ConstructionRules.line_from_points l j) as LJ.
    euclid_apply (TransferInferences.between_if k i j).
    euclid_apply (TransferInferences.between_if b e c).
    euclid_apply (proposition_4 k j l b c a HI LJ KL BC AC AB).
    euclid_apply (MetricInferences.area_congruence k j l b c a).
    euclid_apply (proposition_42' l k j d1 d2 d3 i KL HI LJ D12 D23) as f g FG FI GJ.
    exists f.
    exists g.
    exists j.
    exists FG.
    exists FI.
    exists GJ.
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_42''' : forall (a b c d1 d2 d3 h i x : Point) (AB BC AC D12 D23 HI : Line),
    Triangle a b c AB BC AC /\ RectilinearAngle d1 d2 d3 D12 D23 /\ ~(x on_line HI) /\
    angle2real (AnglePPP d1 d2 d3) > 0 /\ angle2real (AnglePPP d1 d2 d3) < RightAngle + RightAngle /\
    DistinctPointsOnL h i HI ->
    exists (f g j : Point) (FG FI GJ : Line), SameSide f x HI /\ Between h i j /\ Parallelogram f g i j FG HI FI GJ /\ 
    (AnglePPP j i f == AnglePPP d1 d2 d3)%angle /\
    (area2real (AreaPPP f i j) + area2real (AreaPPP f j g) = area2real (AreaPPP a b c)).
Proof.
    euclid_intros.
    euclid_apply (proposition_10 b c BC) as e.
    euclid_apply (ConstructionRules.extend_point_longer HI h i (SegmentPP e c)) as i'.
    euclid_apply (proposition_3' i i' e c HI BC) as j.
    euclid_apply (ConstructionRules.extend_point_longer HI i h (SegmentPP e c)) as h'.
    euclid_apply (proposition_3' i h' e c HI BC) as k.
    euclid_apply (proposition_23''' k j b a c x HI AB BC) as l'.
    destruct Hl'1.
    { euclid_trivial. }
    euclid_apply (ConstructionRules.line_from_points k l') as KL.
    euclid_apply (ConstructionRules.extend_point_longer KL k l' (SegmentPP a b)) as l''.
    euclid_apply (proposition_3' k l'' b a KL AB) as l.
    euclid_apply (ConstructionRules.line_from_points l j) as LJ.
    euclid_apply (TransferInferences.between_if k i j).
    euclid_apply (TransferInferences.between_if b e c).
    euclid_apply (proposition_4 k j l b c a HI LJ KL BC AC AB).
    euclid_apply (MetricInferences.area_congruence k j l b c a).
    euclid_apply (proposition_42' l k j d1 d2 d3 i KL HI LJ D12 D23) as f g FG FI GJ.
    exists f.
    exists g.
    exists j.
    exists FG.
    exists FI.
    exists GJ.
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_43 : forall (a b c d e f g h k : Point) (AD BC AB CD AC EF GH : Line), 
    Parallelogram a d b c AD BC AB CD /\ DistinctPointsOnL a c AC /\ k on_line AC /\
    Between a h d /\ Parallelogram a h e k AD EF AB GH /\ Parallelogram k f g c EF BC GH CD ->
    (area2real (AreaPPP e b g) + area2real (AreaPPP e g k) = area2real (AreaPPP h k f) + area2real (AreaPPP h f d)).
Proof.
    euclid_intros.
    euclid_apply (proposition_34 d a c b AD BC CD AB AC).
    euclid_apply (proposition_34 h a k e AD EF GH AB AC).
    euclid_apply (proposition_34 f k c g EF BC CD GH AC).
    euclid_trivial (area2real (AreaPPP a e k) + area2real (AreaPPP k g c) = area2real (AreaPPP a h k) + area2real (AreaPPP k f c)).
    euclid_apply (TransferInferences.sum_areas_if a c k b AC).
    euclid_apply (TransferInferences.sum_areas_if a b e c AB).
    euclid_apply (TransferInferences.sum_areas_if b c g k BC).
    euclid_trivial (area2real (AreaPPP a e k) + area2real (AreaPPP k g c) + area2real (AreaPPP e b g) + area2real (AreaPPP e g k) = area2real (AreaPPP b a c)).
    euclid_apply (TransferInferences.sum_areas_if a c k d AC).
    euclid_apply (TransferInferences.sum_areas_if a d h k AD).
    euclid_apply (TransferInferences.sum_areas_if c d f k CD).
    euclid_trivial (area2real (AreaPPP a h k) + area2real (AreaPPP k f c) + area2real (AreaPPP h k f) + area2real (AreaPPP h f d) = area2real (AreaPPP d a c)).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_44 : forall (a b c1 c2 c3 d1 d2 d3 : Point) (AB C12 C23 C31 D12 D23 : Line),
    Triangle c1 c2 c3 C12 C23 C31 /\ RectilinearAngle d1 d2 d3 D12 D23 /\ DistinctPointsOnL a b AB /\ 
    angle2real (AnglePPP d1 d2 d3) > 0 /\ angle2real (AnglePPP d1 d2 d3) < RightAngle + RightAngle ->
    exists (m l : Point) (BM AL ML : Line), Parallelogram b m a l BM AL AB ML /\ 
    (AnglePPP a b m == AnglePPP d1 d2 d3)%angle /\
    (area2real (AreaPPP a b m) + area2real (AreaPPP a l m) = area2real (AreaPPP c1 c2 c3)).
Proof.
    euclid_intros.
    euclid_apply (proposition_42'' c1 c2 c3 d1 d2 d3 a b C12 C23 C31 D12 D23 AB) as g f e FG BG EF.
    euclid_apply (proposition_31 a b g BG) as AH.
    euclid_apply (proposition_30 AH EF BG).
    euclid_apply (ConstructionRules.intersection_lines AH FG) as h.
    euclid_apply (ConstructionRules.line_from_points h b) as HB.
    euclid_apply (proposition_29''''' e a f h EF AH FG).
    euclid_trivial (angle2real (AnglePPP b h g) + angle2real (AnglePPP e f h) < RightAngle + RightAngle).
    euclid_trivial (IntersectsLL HB EF).
    euclid_apply (ConstructionRules.intersection_lines HB EF) as k.
    euclid_apply (proposition_31 k e a AB) as KL.
    euclid_apply (proposition_30 KL FG AB).
    euclid_apply (ConstructionRules.intersection_lines AH KL) as l.
    euclid_apply (ConstructionRules.intersection_lines BG KL) as m.
    euclid_trivial (Parallelogram h l f k AH EF FG KL).
    euclid_apply (proposition_43 h f k l g m e a b AH EF FG KL HB BG AB).
    euclid_trivial (area2real (AreaPPP a b m) + area2real (AreaPPP a m l) = area2real (AreaPPP c1 c2 c3)).
    euclid_apply (proposition_15 e a m g b AB BG).
    exists m.
    exists l.
    exists BG.
    exists AH.
    exists KL.
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_44' : forall (a b c1 c2 c3 d1 d2 d3 x : Point) (AB C12 C23 C31 D12 D23 : Line),
    Triangle c1 c2 c3 C12 C23 C31 /\ RectilinearAngle d1 d2 d3 D12 D23 /\ DistinctPointsOnL a b AB /\ ~(x on_line AB) /\
    angle2real (AnglePPP d1 d2 d3) > 0 /\ angle2real (AnglePPP d1 d2 d3) < RightAngle + RightAngle ->
    exists (m l : Point) (BM AL ML : Line), OppositeSide m x AB /\ Parallelogram b m a l BM AL AB ML /\ 
    (AnglePPP a b m == AnglePPP d1 d2 d3)%angle /\
    (area2real (AreaPPP a b m) + area2real (AreaPPP a l m) = area2real (AreaPPP c1 c2 c3)).
Proof.
    euclid_intros.
    euclid_apply (proposition_42''' c1 c2 c3 d1 d2 d3 a b x C12 C23 C31 D12 D23 AB) as g f e FG BG EF.
    euclid_apply (proposition_31 a b g BG) as AH.
    euclid_apply (proposition_30 AH EF BG).
    euclid_apply (ConstructionRules.intersection_lines AH FG) as h.
    euclid_apply (ConstructionRules.line_from_points h b) as HB.
    euclid_apply (proposition_29''''' e a f h EF AH FG).
    euclid_trivial (angle2real (AnglePPP b h g) + angle2real (AnglePPP e f h) < RightAngle + RightAngle).
    euclid_trivial (IntersectsLL HB EF).
    euclid_apply (ConstructionRules.intersection_lines HB EF) as k.
    euclid_apply (proposition_31 k e a AB) as KL.
    euclid_apply (proposition_30 KL FG AB).
    euclid_apply (ConstructionRules.intersection_lines AH KL) as l.
    euclid_apply (ConstructionRules.intersection_lines BG KL) as m.
    euclid_trivial (Parallelogram h l f k AH EF FG KL).
    euclid_apply (proposition_43 h f k l g m e a b AH EF FG KL HB BG AB).
    euclid_trivial (area2real (AreaPPP a b m) + area2real (AreaPPP a m l) = area2real (AreaPPP c1 c2 c3)).
    euclid_apply (proposition_15 e a m g b AB BG).
    exists m.
    exists l.
    exists BG.
    exists AH.
    exists KL.
    euclid_trivial.
all: fail. Admitted.
