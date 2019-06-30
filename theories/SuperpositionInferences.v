Require Import Sorts.

Axiom SAS : forall (a b c d g h : Point) (L : Line), 
    ~(Between b a c) /\ ~(Between a b c) /\ ~(Between a c b) /\
    d on_line L /\ g on_line L /\ ~(h on_line L) -> 
    exists (b' c' : Point), (Angle_PPP d b' c' == Angle_PPP a b c)%angle /\ 
        b' on_line L /\ ~(Between b' d g) /\ (SameSide c' h L) /\ 
        (Segment_PP d b' == Segment_PP a b)%segment /\
        (Segment_PP b' c' == Segment_PP b c)%segment /\
        (Segment_PP c' d == Segment_PP c a)%segment.