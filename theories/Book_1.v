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
