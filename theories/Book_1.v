Add ML Path "/Users/yangky/.opam/4.07.1+flambda/lib/z3".
Require Import SystemE.Axioms.


Theorem proposition_1 : forall (a b : Point) (AB : Line), DistinctPointsOnL a b AB ->
    exists c : Point, (SegmentPP c a == SegmentPP c b == SegmentPP a b)%segment.
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
Theorem proposition_1' : forall (a b f : Point) (AB : Line), 
    DistinctPointsOnL a b AB /\ ~(f on_line AB) ->
    exists c : Point, 
    (SegmentPP c a == SegmentPP c b == SegmentPP a b)%segment /\ (OppositeSide c f AB).
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


Theorem proposition_2 : forall (a b c : Point) (BC : Line), DistinctPointsOnL b c BC ->
    exists l : Point, (SegmentPP a l == SegmentPP b c)%segment.
Proof.
    euclid_intros.
    euclid_case (a = b).
    + exists c.
        euclid_trivial.
    + euclid_apply (ConstructionRules.line_from_points a b) as AB.
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


Theorem proposition_3 : forall (a b c0 c1 : Point) (AB C : Line), 
    DistinctPointsOnL a b AB /\ DistinctPointsOnL c0 c1 C /\ (SegmentPP a b > SegmentPP c0 c1)  ->
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


Theorem proposition_4 : forall (a b c d e f : Point) (AB BC AC DE EF DF : Line),
    Triangle a b c AB BC AC /\ Triangle d e f DE EF DF /\
    (SegmentPP a b == SegmentPP d e)%segment /\
    (SegmentPP a c == SegmentPP d f)%segment /\
    (AnglePPP b a c == AnglePPP e d f)%angle -> 
    (SegmentPP b c == SegmentPP e f)%segment /\
    (AnglePPP a b c == AnglePPP d e f)%angle /\
    (AnglePPP a c b == AnglePPP d f e)%angle.
Proof.
    (*
    euclid_intros.
    euclid_apply (ConstructionRules.line_from_points d e) as DE.
    euclid_apply (SuperpositionInferences.SAS a b c d e f DE) as b' c'.
    euclid_trivial (b' = e).
    euclid_trivial (c' = f).
    euclid_trivial.
    *)
Admitted.


(* theorem cannot be represented in canonical form *)
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
    split.
    + euclid_apply (TransferInferences.sum_angles_onlyif b a g c AB GB).
        euclid_apply (TransferInferences.sum_angles_onlyif c a f b AC FC).
        euclid_trivial.
    + euclid_trivial.
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
    + euclid_case (SegmentPP a b < SegmentPP a c). 
       - euclid_apply (proposition_3 c a a b AC AB) as d.
          euclid_apply (ConstructionRules.line_from_points d b) as DB.
          euclid_apply (proposition_4 c d b b a c AC DB BC AB AC BC).
          euclid_trivial.
       - euclid_trivial. 
all:fail. Admitted.


Theorem proposition_7 : forall (a b c d : Point) (AB AC CB AD DB : Line), 
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
    euclid_case (SameSide a b CD).
    + euclid_case (SameSide d b AC).
        - euclid_apply (TransferInferences.sum_angles_onlyif c a d b AC CD).
            euclid_apply (TransferInferences.sum_angles_onlyif d c b a CD DB).
            euclid_trivial.
        - euclid_trivial.
    + euclid_case (SameSide d b AC). 
        - euclid_trivial.
        - euclid_trivial.
all: fail. Admitted.


Theorem proposition_8 : forall (a b c d e f : Point) (AB BC AC DE EF DF : Line), 
    Triangle a b c AB BC AC /\ Triangle d e f DE EF DF /\
    (SegmentPP a b == SegmentPP d e)%segment /\  (SegmentPP a c == SegmentPP d f)%segment /\
    (SegmentPP b c == SegmentPP e f)%segment ->
    (AnglePPP b a c == AnglePPP e d f)%angle.
Proof.
    (*
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
    *)
Admitted.


Theorem proposition_9 : forall (a b c : Point) (AB AC : Line),
    RectilinearAngle b a c AB AC /\ AB <> AC ->
    exists f : Point, f <> a /\ (AnglePPP b a f == AnglePPP c a f)%angle.
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.point_between_points_shorter_than AB a b (SegmentPP a c)) as d.
    euclid_apply (proposition_3 a c a d AC AB) as e.
    euclid_apply (ConstructionRules.line_from_points d e) as DE.
    euclid_apply (proposition_1' d e a DE) as f. 
    exists f. 
    euclid_apply (ConstructionRules.line_from_points f e) as FE.
    euclid_apply (ConstructionRules.line_from_points f d) as FD.
    euclid_apply (ConstructionRules.line_from_points a f) as AF.
    euclid_case (SameSide d e AF).
    + euclid_apply (proposition_7 a f d e AF AB FD AC FE).
       contradiction.
    + (* thanks to Proclus *)
       euclid_case (f on_line AB).
       - euclid_apply (ConstructionRules.extend_point FE f e) as e'.
          euclid_apply (proposition_5 f d e a e' AB DE FE).
          euclid_trivial (AnglePPP d e c > AnglePPP e d f).
          euclid_apply (proposition_5 a d e f c AB DE AC).
          euclid_trivial.
       - euclid_case (f on_line AC).
          * euclid_apply (ConstructionRules.extend_point FD f d) as d'.
            euclid_apply (proposition_5 f e d a d' AC DE FD).
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
    euclid_apply (proposition_3 a c a d AC AB) as e.
    euclid_apply (ConstructionRules.line_from_points d e) as DE.
    euclid_apply (proposition_1' d e a DE) as f. 
    exists f. 
    euclid_apply (ConstructionRules.line_from_points f e) as FE.
    euclid_apply (ConstructionRules.line_from_points f d) as FD.
    euclid_apply (ConstructionRules.line_from_points a f) as AF.
    euclid_case (SameSide d e AF).
    + euclid_apply (proposition_7 a f d e AF AB FD AC FE).
       contradiction.
    + (* thanks to Proclus *)
       euclid_case (f on_line AB).
       - euclid_apply (ConstructionRules.extend_point FE f e) as e'.
          euclid_apply (proposition_5 f d e a e' AB DE FE).
          euclid_trivial (AnglePPP d e c > AnglePPP e d f).
          euclid_apply (proposition_5 a d e f c AB DE AC).
          euclid_trivial.
       - euclid_case (f on_line AC).
          * euclid_apply (ConstructionRules.extend_point FD f d) as d'.
            euclid_apply (proposition_5 f e d a d' AC DE FD).
            euclid_trivial (AnglePPP e d b > AnglePPP d e f).
            euclid_apply (proposition_5 a d e b f AB DE AC).
            euclid_trivial.
          * euclid_apply (proposition_8 a d f a e f AB FD AF AC FE AF).
            euclid_apply (ConstructionRules.intersection_lines AF DE) as g.  (*Some construction rules really need to be automated !!! *)
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
    exists d.
    euclid_apply (proposition_4 c a d c b d AC AB CD BC AB CD).
    euclid_trivial.
all:fail. Admitted.


Theorem proposition_11 : forall (a b c : Point) (AB : Line), 
    DistinctPointsOnL a b AB /\ Between a c b ->
    exists f : Point, ~(f on_line AB) /\ (AnglePPP a c f == RightAngle)%angle.
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.point_between_points_shorter_than AB c a (SegmentPP c b)) as d.
    euclid_apply (proposition_3 c b c d) as e.
    euclid_apply (proposition_1 d e AB) as f.
    euclid_apply (ConstructionRules.line_from_points d f) as DF.
    euclid_apply (ConstructionRules.line_from_points f e) as FE.
    euclid_apply (ConstructionRules.line_from_points f c) as FC.
    exists f.
    euclid_apply (proposition_8 c d f c e f AB DF FC AB FE FC).
    euclid_apply (TransferInferences.perpendicular_if d e c f AB).
    euclid_trivial.
all: fail. Admitted.


Theorem proposition_11' : forall (a b c g : Point) (AB : Line), 
    DistinctPointsOnL a b AB /\ Between a c b /\ ~(g on_line AB) ->
    exists f : Point, (SameSide f g AB) /\ (AnglePPP a c f == RightAngle)%angle.
Proof.
    euclid_intros.
    euclid_apply (ConstructionRules.point_between_points_shorter_than AB c a (SegmentPP c b)) as d.
    euclid_apply (proposition_3 c b c d) as e.
    euclid_apply (ConstructionRules.point_opposite_side AB g) as h.
    euclid_apply (proposition_1' d e h AB) as f.
    euclid_apply (ConstructionRules.line_from_points d f) as DF.
    euclid_apply (ConstructionRules.line_from_points f e) as FE.
    euclid_apply (ConstructionRules.line_from_points f c) as FC.
    exists f.
    euclid_apply (proposition_8 c d f c e f AB DF FC AB FE FC).
    euclid_apply (TransferInferences.perpendicular_if d e c f AB).
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
    + euclid_trivial.
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
           euclid_apply (TransferInferences.flat_angle a b c).
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
    euclid_apply (proposition_3 a c a b AC AB) as d.
    euclid_apply (ConstructionRules.line_from_points b d) as BD.
    euclid_apply (proposition_16 b c d a BC AC BD).
    euclid_apply (ConstructionRules.extend_point AB a b) as e.
    euclid_apply (proposition_5 a b d e c AB BD AC).
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
    +  euclid_apply (ConstructionRules.extend_point AB a b) as d.
        euclid_apply (ConstructionRules.extend_point AC a c) as e.
        euclid_apply (proposition_5 a b c d e AB BC AC).
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
    euclid_apply (proposition_3 a d' a c AB AC) as d.
    euclid_apply (ConstructionRules.line_from_points d c) as DC.
    euclid_apply (ConstructionRules.extend_point AC a c) as c'.
    euclid_apply (proposition_5 a c d c' d' AC DC AB).
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
    euclid_apply (proposition_3 d e a0 a1 DE A) as f.
    euclid_apply (proposition_3 f e b0 b1 DE B) as g.
    euclid_apply (proposition_3 g e c0 c1 DE C) as h.
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
    euclid_apply (proposition_3 f e'' a0 a1 DE A) as d.
    euclid_apply (proposition_3 f e'' b0 b1 DE B) as g.
    euclid_apply (proposition_3 g e'' c0 c1 DE C) as h.
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
    euclid_apply (proposition_3 f e'' a0 a1 DE A) as d.
    euclid_apply (proposition_3 f e'' b0 b1 DE B) as g.
    euclid_apply (proposition_3 g e'' c0 c1 DE C) as h.
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


(* proof different from the book *)
Theorem proposition_23 : forall (a b c d e : Point) (AB CD CE : Line),
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
    + euclid_apply (ConstructionRules.line_from_points d e) as DE.
        euclid_apply (proposition_20 c d e CD DE CE).
        euclid_apply (proposition_20 d e c DE CE CD).
        euclid_apply (proposition_20 e c d CE CD DE).
        euclid_apply (proposition_22' c d c e e d a b CD CE DE AB) as f g.
        euclid_apply (ConstructionRules.line_from_points a f) as AF.
        euclid_apply (ConstructionRules.line_from_points f g) as FG.
        euclid_apply (proposition_8 c d e a f g CD DE CE AF FG AB).
        exists f.
        euclid_apply (TransferInferences.equal_angles a f f g b AF AB).
        euclid_trivial.
all: fail. Admitted.


Theorem proposition_23' : forall (a b c d e x : Point) (AB CD CE : Line), 
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
        euclid_apply (TransferInferences.equal_angles a f f g b AF AB).
        euclid_trivial.
all: fail. Admitted.


Theorem proposition_23'' : forall (a b c d e x : Point) (AB CD CE : Line), 
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