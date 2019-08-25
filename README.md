System E
--------------------------------


## Dependencies

* [OPAM](https://opam.ocaml.org/)
* [Coq == 8.9](https://github.com/coq/coq) installed via OPAM
* [dune >= 1.10](https://opam.ocaml.org/packages/dune/)
* [z3 == 4.8.1] installed via OPAM


## Installation

1. `git clone https://github.com/princeton-vl/system-e && cd system-e`
1. `dune build && dune install`


# Running

```coq
Require Import SystemE.Axioms.

Lemma foo : True.
Proof.
    hello. now auto.
Qed.

Theorem Proposition_1 : forall (a b : Point), a <> b ->
    exists c : Point, Segment_PP c a == Segment_PP c b == Segment_PP a b.
Proof.
    intros.
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
Qed.

```
