Require Import Sorts.

(* different from the original system e *)
Axiom SAS : forall (a b c d g h : Point) (L : Line), 
    ~(Between b a c) /\ ~(Between a b c) /\ ~(Between a c b) /\
    d on_line L /\ g on_line L /\ ~(h on_line L) -> 
    exists (b' c' : Point), (AnglePPP d b' c' == AnglePPP a b c)%angle /\ 
        (AnglePPP b' c' d == AnglePPP b c a)%angle /\
        (AnglePPP c' d b' == AnglePPP c a b)%angle /\
        b' on_line L /\ ~(Between b' d g) /\ (SameSide c' h L) /\ 
        (SegmentPP d b' == SegmentPP a b)%segment /\
        (SegmentPP b' c' == SegmentPP b c)%segment /\
        (SegmentPP c' d == SegmentPP c a)%segment.