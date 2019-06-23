Require Import Sorts.

(*
Axiom SAS : forall (a b c d g h : Point) (L : Line) (P : Prop), 
    ~(Between b a c) /\ ~(Between a b c) /\ (Between a c b) /\
    d on_line L /\ g on_line L /\ ~(h on_line L) -> 
    (((exists (a' b' c' : Point), 
        a' = d /\ (Angle_PPP a'b'c' == Angle_PPP a b c)%angle /\ 
        b' on_line L /\ ~(Between b' d g) /\ (SameSide c' h L)) 
        -> P)
    -> P)*)