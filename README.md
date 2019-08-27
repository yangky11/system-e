System E
--------------------------------


## Dependencies

* [OPAM](https://opam.ocaml.org/)
* [Coq == 8.9.1](https://opam.ocaml.org/packages/coq/) install via OPAM: `opam install coq=8.9.1`
* [dune >= 1.10.0](https://opam.ocaml.org/packages/dune/) install via OPAM: `opam install dune=1.10.0`
* [z3 == 4.8.1](https://opam.ocaml.org/packages/z3/z3.4.8.1/) install via OPAM: `opam install z3=4.8.1`


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
    exists c : Point, SegmentPP c a == SegmentPP c b == SegmentPP a b.
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
